class type range = object  end
class type annotation =
  object
    method column : int Js.prop
    method row : int Js.prop
    method text : Js.js_string Js.t Js.prop
    method type_ : Js.js_string Js.t Js.prop
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
    method hasRedo : bool Js.t Js.meth
    method hasUndo : bool Js.t Js.meth
    method redo : bool Js.t -> unit Js.meth
    method reset : unit Js.meth
    method undo : bool Js.t -> range Js.meth
  end
class type editSession =
  object
    method addMarker :
      range Js.t -> Js.js_string Js.t -> Js.js_string Js.t -> int Js.meth
    method clearAnnotations : unit Js.meth
    method getDocument : document Js.t Js.meth
    method getUndoManager : undoManager Js.t Js.meth
    method on :
      Js.js_string Js.t -> (< .. > Js.t -> unit) Js.callback -> unit Js.meth
    method removeMarker : int -> unit Js.meth
    method setMode : Js.js_string Js.t -> unit Js.meth
    method setAnnotations : annotation Js.t Js.js_array Js.t -> unit Js.meth
  end
class type editor =
  object
    method focus : unit Js.meth
    method getSession : editSession Js.t Js.meth
    method gotoLine : int -> float -> bool Js.t -> unit Js.meth
    method on :
      Js.js_string Js.t -> (< .. > Js.t -> unit) Js.callback -> unit Js.meth
    method resize : bool Js.t -> unit Js.meth
    method setReadOnly : bool Js.t -> unit Js.meth
    method setTheme : Js.js_string Js.t -> unit Js.meth
  end
class type ace =
  object
    method edit : Js.js_string Js.t -> editor Js.t Js.meth
    method require : Js.js_string Js.t -> < .. > Js.t Js.meth
  end
val ace : ace Js.t
val _Range : (int -> int -> int -> int -> range Js.t) Js.constr
val _Document : (Js.js_string -> document) Js.constr
val mk_annotation :
  int -> int -> Js.js_string Js.t -> Js.js_string Js.t -> annotation Js.t
val mk_position : int -> int -> position Js.t
