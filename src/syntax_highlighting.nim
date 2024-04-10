import sequtils, unicode, streams
import pixie
import text
import fusion/matching

const
  OpChars  = ['+', '-', '*', '/', '\\', '<', '>', '!', '?', '^', '.',
              '|', '=', '%', '&', '$', '@', '~', ':']

type
  CodeKind* = enum
    sText

    sComment
    
    sKeyword
    sControlFlow
    sOperator
    sOperatorWord
    sFunction
    sType
    sBuiltinType
    sStringLit
    sCharLit
    sNumberLit
    sError

    sStringLitEscape
    sCharLitEscape

    sTodoComment

    sLineNumber

  NimParseState* = object
    pos: int
    last: CodeKind
    inQuote, inComment: bool
    inMultiline: bool



proc parseNimCode*(s: Text, state: NimParseState, len = 100): tuple[segments: seq[CodeKind], state: NimParseState] =
  result.state = state
  result.segments = newSeq[CodeKind](len)
  let opRunes = OpChars.toRunes
  proc parseNext(s: Text, state: var NimParseState, res: var seq[CodeKind]) =
    template rune(s: string): Rune = static(s.runeAt(0))
    template runes(s: string): seq[Rune] = static(s.toRunes)
    
    template peek(i: int = 0): Rune =
      s[state.pos + i]
    
    template skip(n: int = 1) =
      inc state.pos, n
    
    template exist(n: int): bool =
      state.pos + n < s.len
    
    template add(kind: CodeKind, len: int = 1) =
      let i = len
      for j in state.pos ..< state.pos + i:
        res[j] = kind
      skip i
    
    template set(kind: CodeKind, p: int, len: int = 1) =
      let pp = p
      let i = len
      for j in state.pos + pp ..< state.pos + pp + i:
        res[j] = kind
    
    template ident =
      var l = 1
      
      while true:
        if not exist(l): break
        let r = peek(l)
        if (not r.isAlpha) and (r notin "0123456789_".runes): break
        inc l

      let kind =
        if peek().isUpper:
          sType

        else:
          let id = s[state.pos ..< state.pos + l].toOpenArray.toSeq
          if id in ["func".runes, "proc".runes, "template".runes, "iterator".runes, "converter".runes, "macro".runes, "method".runes, 
            "addr".runes, "asm".runes, "bind".runes, "concept".runes, "const".runes, "discard".runes, "distinct".runes, "enum".runes, "export".runes, "from".runes, 
            "import".runes, "include".runes, "interface".runes, "let".runes, "mixin".runes, "nil".runes, "object".runes, "of".runes, "out".runes, "ptr".runes, 
            "ref".runes, "static".runes, "tuple".runes, "type".runes, "using".runes, "var".runes, "true".runes, "false".runes, "off".runes, "on".runes, "low".runes,
            "high".runes, "lent".runes, "sink".runes]:
            sKeyword

          elif id in  ["block".runes, "break".runes, "case".runes, "continue".runes, "defer".runes, "do".runes, "elif".runes, "else".runes, "end".runes, "except".runes, 
            "finally".runes, "for".runes, "if".runes, "raise".runes, "return".runes, "try".runes, "when".runes, "while".runes, "yield".runes]:
            sControlFlow
          
          elif id in ["and".runes, "as".runes, "cast".runes, "div".runes, "in".runes, "isnot".runes, "is".runes, "mod".runes, "notin".runes, "not".runes, "or".runes, "shl".runes, "shr".runes, "xor".runes, "echo".runes]:
            sOperatorWord
          
          elif id in ["int8".runes, "int16".runes, "int32".runes, "int64".runes, "uint8".runes, "uint16".runes, "uint32".runes, "uint64".runes, "float32".runes, "float64".runes, 
            "int".runes, "float".runes, "string".runes, "bool".runes, "byte".runes, "uint".runes, "seq".runes, "set".runes, "char".runes, "void".runes, "auto".runes, "any".runes, "pointer".runes]:
            sBuiltinType
        
          elif exist(l) and (peek(l) == "(".rune or peek(l) == "\"".rune):
            sFunction
        
          else: sText
      
      add kind, l
    
    template comment =
      var l = 1
      var isTodo: bool
      var wasAlpha: bool

      template checkTodo =
        if (not wasAlpha) and (not isTodo) and (
          (peek(l).toLower == rune"t") and
          (exist(l + 1) and peek(l + 1).toLower == rune"o") and
          (exist(l + 2) and peek(l + 2).toLower == rune"d") and
          (exist(l + 3) and peek(l + 3).toLower == rune"o") and
          (exist(l + 4) and (not peek(l + 4).isAlpha))
        ):
          isTodo = true
          inc l, 4
          continue

        elif (not wasAlpha) and (not isTodo) and (
          (peek(l).toLower == rune"t") and
          (exist(l + 1) and peek(l + 1).toLower == rune"o") and
          (exist(l + 2) and peek(l + 2).isWhiteSpace) and
          (exist(l + 3) and peek(l + 3).toLower == rune"d") and
          (exist(l + 4) and peek(l + 4).toLower == rune"o") and
          (exist(l + 5) and (not peek(l + 5).isAlpha))
        ):
          isTodo = true
          inc l, 5
          continue
      
      if exist(l) and peek(l) == rune"[":  # multiline comment
        while true:
          if not exist(l): break
          checkTodo
          if (
            (peek(l) == rune"]") and
            (exist(l + 1) and peek(l + 1) == rune"#")
          ): 
            inc l, 2
            break
          if (not wasAlpha) and (peek(l).isAlpha): wasAlpha = true
          inc l
      
      else:  # single line comment
        while true:
          if not exist(l): break
          checkTodo
          let r = peek(l)
          if r == "\n".rune: break
          if (not wasAlpha) and (r.isAlpha): wasAlpha = true
          inc l
      
      if isTodo: add sTodoComment, l
      else:      add sComment, l
    
    template number =
      var l = 1
      var wasDot: bool
      var wasQuote: bool
      var digits = "0123456789_".runes

      if (peek(0) == rune"0") and ((peek(l) == rune"x") or (peek(l) == rune"X")) and exist(l + 1) and (peek(l + 1) in "0123456789abcdefABCDEF_".runes):
        inc l
        digits = "0123456789abcdefABCDEF_".runes
      
      elif (peek(0) == rune"0") and ((peek(l) == rune"o") or (peek(l) == rune"O")) and exist(l + 1) and (peek(l + 1) in "01234567_".runes):
        inc l
        digits = "01234567_".runes
      
      elif (peek(0) == rune"0") and ((peek(l) == rune"b") or (peek(l) == rune"B")) and exist(l + 1) and (peek(l + 1) in "01_".runes):
        inc l
        digits = "01_".runes

      while true:
        if not exist(l): break
        let r = peek(l)
        if wasQuote:
          if (not r.isAlpha) and (r notin "0123456789_".runes):
            break
        else:
          if (not wasDot) and (r == rune"."):
            wasDot = true
          elif (not wasQuote) and (r == rune"'") and exist(l + 1) and (peek(l + 1).isAlpha):
            wasQuote = true
          elif (r notin digits):
            break
        inc l
      
      add sNumberLit, l
      # todo: errors in numbers

    template escape(r, l, onError, onEscape) {.dirty.} =
      if r == "\\".rune:
        inc l

        template nishex(i): bool = exist(l + i) and peek(l + i) in "0123456789abcdefABCDEF".runes

        if exist(l) and peek(l) in "nrt\\0'\"?abfv".runes:
          let n {.used.} = 2
          onEscape
          inc l
          continue
        
        elif exist(l) and peek(l) == rune"X":
          if nishex(1) and nishex(2):
              let n {.used.} = 4
              onEscape
              inc l, 3
              continue
          onError
        
        elif exist(l) and peek(l) == rune"u":
          if nishex(1) and nishex(2) and nishex(3) and nishex(4):
              let n {.used.} = 6
              onEscape
              inc l, 5
              continue
          onError
        
        elif exist(l) and peek(l) == rune"U":
          if nishex(1) and nishex(2) and nishex(3) and nishex(4) and nishex(5) and nishex(6) and nishex(7) and nishex(8):
              let n {.used.} = 10
              onEscape
              inc l, 9
              continue
          onError
        
        elif exist(l) and peek(l) in "012".runes:
          if exist(l + 1) and peek(l + 1) in "012345".runes:
            if exist(l + 2) and peek(l + 2) in "0123456789".runes:
              let n {.used.} = 4
              onEscape
              inc l, 3
              continue
          onError
        
        else:
          onError

    template str =
      var l = 1
      var isError: bool
      var sets: seq[(CodeKind, int, int)]
      
      while true:
        if not exist(l): isError = true; break
        let r = peek(l)
        escape(r, l) do:
          sets.add (sError, l - 1, 2)
        do:
          sets.add (sStringLitEscape, l - 1, n)
        inc l
        if r == "\"".rune: break
        if r == "\n".rune: isError = true; break
      
      if isError:
        add sError, l
      else:
        add sStringLit, l
        skip -l
        for (k, p, n) in sets:
          set k, p, n
        skip l
  
    template multilineStr =
      var l = 1
      var isError: bool
      var sets: seq[(CodeKind, int, int)]
      var quoteCount = 0

      while true:
        if not exist(l): isError = true; break
        let r = peek(l)
        escape(r, l) do:
          sets.add (sError, l - 1, 2)
        do:
          sets.add (sStringLitEscape, l - 1, n)
        inc l
        if r == "\"".rune:
          inc quoteCount
          if quoteCount == 3: break
        else:
          quoteCount = 0
      
      if isError:
        add sError, l
      else:
        add sStringLit, l
        skip -l
        for (k, p, n) in sets:
          set k, p, n
        skip l
    
    # todo: raw strings

    template chr =
      var l = 1
      var isError: bool
      var isEscape: bool
      
      while true:
        if not exist(l): isError = true; break
        let r = peek(l)
        escape(r, l) do:
          isError = true
        do:
          if isEscape: isError = true
          isEscape = true
        inc l
        if r == rune"'": break
        if r == "\n".rune: isError = true; break
        if l > 2: isError = true
      
      if isError:
        add sError, l
      elif isEscape:
        add sStringLitEscape, l
      else:
        add sStringLit, l

    let r = peek()
    if r.isAlpha:                  ident
    elif r == rune"'":             chr
    elif r == rune"#":             comment
    elif r in "0123456789".runes:  number
    elif r in opRunes:
      add sOperator, 1

    elif r == "\"".rune and peek(1) == r and peek(2) == r:
      multilineStr
    
    elif r == "\"".rune:           str
    else:
      add sText

  for _ in 1..len:
    if result.state.pos > s.high: return
    s.parseNext(result.state, result.segments)
