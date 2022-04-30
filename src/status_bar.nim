import std/unicode
import pixwindy, pixie
import render, configuration, markup

component StatusBar:
  proc handle(
    gt: var GlyphTable,
    bg: ColorRgb,
    fieldsStart: seq[tuple[field: string, value: string]],
    fieldsEnd: seq[tuple[field: string, value: string]],
  )

  const margin = vec2(8, 2)
  const marginEnd = vec2(0, 2)
  var s = ""

  let box = parentBox

  for i in fieldsStart:
    s.add(i.field & i.value & "   ")
  
  r.fillStyle = bg
  r.fillRect box

  image.draw toRunes(s), colorTheme.cInActive, box.xy + margin, rect(box.xy, box.wh - margin), gt, bg

  s = ""

  for i in fieldsEnd:
    if(i.field == "git: "):
      s.add(i.value & "   ")
    else:
      s.add(i.field & i.value & "   ")

  let start = box.xy + vec2(box.w - toRunes(s).width(gt).float32, 0) + marginEnd

  for i in fieldsEnd:
    if(i.field == "git: "):
      image.draw(iconTheme.git, translate(start - vec2(10, -2)))

  image.draw toRunes(s), colorTheme.cInActive, start, rect(box.xy, box.wh), gt, bg