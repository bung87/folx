import std/sequtils, os, std/unicode, math, std/algorithm
import gui, configuration

type 
  File* = object
    path*: string
    dir*: string
    name*: string
    ext*: string
    open*: bool
    files*: seq[File]
    info*: FileInfo
  
  OpenDir* = object
    path*: string
  
  SideExplorer* = object
    current_dir*: string
    current_item*: PathComponent
    current_item_name*: string
    current_item_path*: string
    current_item_ext*: string
    count_items*: int
    pos*: float32
    y*: float32
    item_index*: int
    dir*: File
    display*: bool
    open_dirs*: seq[OpenDir]
    new_dir_item_index*: bool 

proc nameUpCmp*(x, y: File): int =
  if x.name & x.ext >= y.name & y.ext: 1
  else: -1

proc folderUpCmp*(x, y: File): int =
  if (x.info.kind, y.info.kind) == (PathComponent.pcFile, PathComponent.pcDir): 1
  else: -1

proc folderDownCmp*(x, y: File): int =
  if (x.info.kind, y.info.kind) == (PathComponent.pcDir, PathComponent.pcFile): 1
  else: -1

proc bySizeUpCmp*(x, y: File): int =
  if x.info.size < y.info.size: 1
  else: -1

proc bySizeDownCmp*(x, y: File): int =
  if x.info.size > y.info.size: 1
  else: -1


proc getIcon(explorer: SideExplorer, file: File): Image =
  if file.info.kind == PathComponent.pcFile:
    case file.ext
    of ".nim": result = iconTheme.nim
    else: 
      case file.name
      of ".gitignore": result = iconTheme.gitignore
      else: result = iconTheme.file
  elif file.info.kind == PathComponent.pcDir:
    if OpenDir(path: file.path / file.name & file.ext) in explorer.open_dirs:
      result = iconTheme.openfolder
    else:
      result = iconTheme.folder

proc newFiles(file_path: string): seq[File] =
  var info: FileInfo
  var files: seq[File] = @[]
  
  for file in walkDir(file_path):
    try:
      let (dir, name, ext) = splitFile(file.path)
      info = getFileInfo(file.path)

      var new_file = File(
        path: file_path,
        dir: dir,
        name: name,
        ext: ext,
        open: false,
        files: @[],
        info: info
      )
      files.add(new_file)
    except CatchableError: discard

  return files


proc updateDir*(explorer: var SideExplorer, path: string) =
  let (dir, name, ext) = splitFile(explorer.current_dir)
  let info = getFileInfo(explorer.current_dir)
  explorer.dir = File(
    path: explorer.current_dir,
    dir: dir,
    name: name,
    ext: ext,
    open: false,
    files: newFiles(explorer.current_dir),
    info: info,
  )

proc onKeydown*(
  explorer: var SideExplorer,
  e: KeyEvent,
  path: string,
  onFileOpen: proc(file: string)
  ) =
  case e.key
  of Key.left:
    if explorer.current_item == PathComponent.pcDir:
      explorer.open_dirs = explorer.open_dirs.filterIt(it != OpenDir(path: explorer.current_item_path / explorer.current_item_name & explorer.current_item_ext))
    
  of Key.up:
    if explorer.item_index > 1:
      dec explorer.item_index
  
  of Key.down:
    if explorer.item_index < explorer.count_items:
      inc explorer.item_index

  of Key.right:
    if explorer.current_item == PathComponent.pcFile:
      onFileOpen(explorer.current_item_path / explorer.current_item_name & explorer.current_item_ext)
    elif explorer.current_item == PathComponent.pcDir:
      explorer.open_dirs.add(OpenDir(path: explorer.current_item_path / explorer.current_item_name & explorer.current_item_ext))

  else: discard


proc updateExplorer(explorer: var SideExplorer, file: File) =
  explorer.current_item = file.info.kind
  explorer.current_item_path = file.path
  explorer.current_item_name = file.name
  explorer.current_item_ext = file.ext

component Item {.noexport.}:
  proc handle(
    explorer: var SideExplorer,
    file: File,
    nesting_indent: int,
    text: string,
    icon_const: float32,
    count_item: int,
    selected: bool,
    open_file: proc(file: string)
  )

  let
    gt = glyphTableStack[^1]
    dy = round(gt.font.size * 1.40)

  if selected:
    updateExplorer(explorer, file)

    Rect: color = colorTheme.bgSelection.color
    Rect(w = 2): color = colorTheme.bgSelectionLabel.color

  if isLeftClick and mouseHover parentBox:
    if file.info.kind == PathComponent.pcFile:
      open_file(file.path / file.name & file.ext)
    elif file.info.kind == PathComponent.pcDir:
      if OpenDir(path: file.path / file.name & file.ext) in explorer.open_dirs:
        explorer.open_dirs = explorer.open_dirs.filterIt(it != OpenDir(path: file.path / file.name & file.ext))
      else:
        explorer.open_dirs.add(OpenDir(path: file.path / file.name & file.ext))
    explorer.item_index = count_item 
  
  let icon = getIcon(explorer, file)
  Image icon(x = 20 + nesting_indent.float32 * 20, y = 4, w = icon.width.float * icon_const * dy, h = icon.height.float * icon_const * dy):
    discard

  Text text(x = 20 + nesting_indent.float32 * 20 + 20):
    color = colorTheme.cActive
    bg = if selected: colorTheme.bgSelection else: colorTheme.bgExplorer

  explorer.y += dy # todo: move this out

component Title {.noexport.}:
  proc handle(
    explorer: var SideExplorer,
  )

  let
    gt = glyphTableStack[^1]
    dy = round(gt.font.size * 1.40)

  Text "Explorer"(horisontalCenterIn = parentBox, w = "Explorer".toRunes.width(gt), h = dy):
    color = colorTheme.cActive
    bg = colorTheme.bgExplorer
  explorer.y += dy

  Text explorer.dir.path(y = dy):
    color = colorTheme.cInActive
    bg = colorTheme.bgExplorer
  explorer.y += dy


component SideExplorer:
  proc handle(
    explorer: var SideExplorer,
    dir: File,
    nesting: int32 = 0,
    onFileOpen: proc(file: string)
  )

  var box = parentBox
  let
    gt = glyphTableStack[^1]
    dy = round(gt.font.size * 1.40)
    icon_const = 0.06
  var
    dir = dir
    size = (box.h / gt.font.size).ceil.int
    count_items = explorer.count_items
    pos = explorer.pos

  
  if nesting == 0:
    explorer.y = 0
    count_items = 0
    explorer.count_items = 0

    Rect: color = colorTheme.bgExplorer.color
    
    Title(h = dy * 2):
      explorer = explorer

  #! sorted on each component rerender
  # todo: check if seq already sorted or take the sort to updateDir

  var dir_files: seq[File] = @[]
  var dir_folders: seq[File] = @[]
  for file in dir.files:
    if file.info.kind == PathComponent.pcFile:
      dir_files.add(file)
    elif file.info.kind == PathComponent.pcDir:
      dir_folders.add(file)


  sort(dir_files, nameUpCmp)
  sort(dir_folders, nameUpCmp)
  dir.files = dir_folders & dir_files
  
  for i, file in dir.files.pairs:
    inc count_items

    let text = file.name & file.ext

    if count_items in pos.int..pos.ceil.int+size:
      Item(y = explorer.y, h = dy):
        explorer = explorer
        file = file
        nesting_indent = nesting
        text = text
        icon_const = icon_const
        count_item = count_items
        selected = count_items == int(explorer.item_index)
        open_file = (proc(file: string) =
          onFileOpen file
        )
    
    if file.info.kind == PathComponent.pcDir:
      if OpenDir(path: file.path / file.name & file.ext) in explorer.open_dirs:

        dir.files[i].files = newFiles(file.path / file.name & file.ext)

        explorer.count_items = count_items

        SideExplorer explorer(top = 0, bottom = 0, w = 260):
          dir = dir.files[i]
          nesting = nesting + 1
          onFileOpen = (proc(file: string) =
            onFileOpen file
          )
          
        
        count_items = explorer.count_items

  explorer.count_items = count_items
