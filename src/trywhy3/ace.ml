open Js

class type range =
  object
  end

class type annotation =
  object
    method row : int prop
    method column : int prop
    method text : js_string t prop
    method type_ : js_string t prop
  end

class type position =
  object
    method column : int Js.prop
    method row : int Js.prop
  end

class type document =
  object
    method getLength : int Js.meth
    method getValue : Js.js_string Js.t Js.meth
    method indexToPosition :
      int -> int -> position Js.t Js.meth
    method on :
      Js.js_string Js.t -> (< .. > Js.t -> unit) Js.callback -> unit Js.meth
    method positionToIndex :
             position Js.t -> int -> int Js.meth
    method setNewlineMode : Js.js_string Js.t -> unit Js.meth
    method setValue : Js.js_string Js.t -> unit Js.meth
  end


class type undoManager =
  object
    method hasRedo : bool t meth
    method hasUndo : bool t meth
    method redo : bool t -> unit meth
    method undo : bool t -> range meth
    method reset : unit meth
  end


class type editSession =
  object
    method addMarker : range t -> js_string t -> js_string t -> int meth
    method clearAnnotations : unit meth
    method getDocument : document t meth
    method getUndoManager : undoManager t meth
    method removeMarker : int -> unit meth
    method setAnnotations : annotation t js_array t -> unit meth
    method setMode : js_string t -> unit meth
    method on : js_string t -> (< .. > t -> unit) callback -> unit meth
    method setUseSoftTabs : bool Js.t -> unit Js.meth
  end

class type editor =
  object
    method focus : unit meth
    method getSession : editSession t meth
    method resize : bool t -> unit meth
    method setReadOnly : bool t -> unit meth
    method gotoLine : int -> float -> bool t -> unit meth
    method setTheme : Js.js_string Js.t -> unit meth
    method on : js_string t -> (< .. > t -> unit) callback -> unit meth
  end

class type ace =
  object
    method require : js_string t -> (< .. > as 'a) t meth
    method edit : js_string t -> editor t meth
  end

let log s = Firebug.console ## log (Js.string s)

let check_def s o =
  Js.Optdef.get o (fun () -> log ("Property " ^ s ^ " is undefined or null");
			  assert false)

let get o ident =
  let res : 'a Js.optdef = Js.Unsafe.(get o) (Js.string ident) in
  check_def ident res

let global ident =
  get Js.Unsafe.global ident

let ace : ace t = global "ace"

let _Range : (int -> int -> int -> int -> range t) constr =
  let r = ace ## require (Js.string "ace/range") in
  get r "Range"


let _Document : (js_string -> document) constr =
  let d = ace ## require (Js.string "ace/document") in
  get d "Document"

let mk_annotation (row : int) (col : int) (text : js_string t) (kind : js_string t) : annotation t =
  Js.Unsafe.(obj [| "row", inject row; "column", inject col;
	            "text", inject text; "type", inject kind |])

let mk_position (row : int) (col : int) : position t =
    Js.Unsafe.(obj [| "row", inject row; "column", inject col |])
