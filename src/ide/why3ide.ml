
(*
open Format
open Why3
open Gconfig
open Stdlib
open Session_itp
open Controller_itp
open Session_user_interface
open Historic
*)

open Why3
open Itp_server
open Gconfig
open Session_user_interface.Historic
open Stdlib

external reset_gc : unit -> unit = "ml_reset_gc"

let debug = Debug.lookup_flag "ide_info"

module Server = Make (Protocol.Protocol_why3ide)

module type Protocol = sig

  val send_request: ide_request -> unit
  val get_notified: unit -> notification list

end

module Make (P: Protocol) = struct

(* TODO add at end *)
(*  let treat_notifications () = ?????
  let treat_user_inputs () = ?????

  let _ = Unix_Scheduler.idle ~prio:1 treat_notifications
  let _ = Unix_Scheduler.idle ~prio:1 treat_user_interface
*)
(* TODO adapt the rest *)

(* Global initialization has not yet been done *)
let is_init = ref false
(* Initial config is empty *)
(* TODO *)
let gconfig = Gconfig.default_config
let main_dir = ref ""

(* TODO temp globals *)
let provers_list = ref []
let transformation_list = ref []
let strategy_list = ref []
let commands : string list ref = ref []

(* -------------- Library -------------------- *)

(* TODO
let _ =
  let treat_user_inputs () =
  (* Before accepting user inputs, open a file *)
  (* TODO right now the server initialize by default
     P.send_requests (Init usage_str spec)*)
    let l = P.get_notified () in
    treat_requests init l
*)

(*
let task_driver =
  let main = Whyconf.get_main gconfig.config in
  let d = Filename.concat (Whyconf.datadir main)
                          (Filename.concat "drivers" "why3_itp.drv")
  in
  Driver.load_driver gconfig.env d []
*)

(*
let provers : Whyconf.config_prover Whyconf.Mprover.t =
  Whyconf.get_provers gconfig.config

let cont =
  try
    Session_user_interface.cont_from_files spec usage_str gconfig.env files provers
  with e ->
       eprintf "%a@." Exn_printer.exn_printer e;
       exit 1
*)


(********************************)
(* Source language highlighting *)
(********************************)

let (why_lang, any_lang) =
(*  let main = Whyconf.get_main gconfig.config in*)
  let load_path = Filename.concat !main_dir "lang" in
  let languages_manager =
    GSourceView2.source_language_manager ~default:true
  in
  languages_manager#set_search_path
    (load_path :: languages_manager#search_path);
  let why_lang =
    match languages_manager#language "why3" with
    | None ->
        Format.eprintf "language file for 'why3' not found in directory %s@."
          load_path;
        exit 1
    | Some _ as l -> l in
  let any_lang filename =
    match languages_manager#guess_language ~filename () with
    | None -> why_lang
    | Some _ as l -> l in
  (why_lang, any_lang)

(* Borrowed from Frama-C src/gui/source_manager.ml:
Try to convert a source file either as UTF-8 or as locale. *)
let try_convert s =
  try
    if Glib.Utf8.validate s then s else Glib.Convert.locale_to_utf8 s
  with Glib.Convert.Error _ ->
    try
      Glib.Convert.convert_with_fallback
        ~fallback:"#neither UTF-8 nor locale nor ISO-8859-15#"
        ~to_codeset:"UTF-8"
        ~from_codeset:"ISO_8859-15"
        s
    with Glib.Convert.Error _ as e -> Printexc.to_string e



(**********************)
(* Graphical elements *)
(**********************)

let main_window =
  let w = GWindow.window
            ~allow_grow:true ~allow_shrink:true
            ~width:gconfig.window_width
            ~height:gconfig.window_height
            ~title:"Why3 Interactive Proof Session" ()
  in
  (* callback to record the new size of the main window when changed, so
   that on restart the window size is the same as the last session *)
  let (_ : GtkSignal.id) =
    w#misc#connect#size_allocate
      ~callback:
      (fun {Gtk.width=w;Gtk.height=h} ->
       gconfig.window_height <- h;
       gconfig.window_width <- w)
  in w

(* the main window contains a vertical box, containing:
   1. the menu
   2. an horizontal box
 *)

let vbox = GPack.vbox ~packing:main_window#add ()

let menubar = GMenu.menu_bar
  ~packing:(vbox#pack ?from:None ?expand:None ?fill:None ?padding:None)
  ()

let hb = GPack.hbox ~packing:vbox#add ()

(* 1. Menu *)

let factory = new GMenu.factory menubar

let accel_group = factory#accel_group

(* 1.1 "File" menu *)

let file_menu = factory#add_submenu "_File"
let file_factory = new GMenu.factory file_menu ~accel_group

let exit_function ~destroy () =
  ignore(destroy); GMain.quit ()

let (_ : GtkSignal.id) = main_window#connect#destroy
  ~callback:(exit_function ~destroy:true)

let (_ : GMenu.menu_item) =
  file_factory#add_item ~key:GdkKeysyms._S "_Save session"
    ~callback:(fun () -> P.send_request (Save, ""))

let (replay_menu_item : GMenu.menu_item) =
  file_factory#add_item ~key:GdkKeysyms._R "_Replay all"

let (_ : GMenu.menu_item) =
  file_factory#add_item ~key:GdkKeysyms._Q "_Quit"
    ~callback:(fun x -> exit_function ~destroy:false x; P.send_request (Exit, ""))


(* 1.2 "View" menu

   the entries in that menu are defined later

*)

(* 2. horizontal box contains:
   2.1 TODO: a tool box ?
   2.2 a horizontal paned containing:
     2.2.1 a scrolled window to hold the tree view of the session
     2.2.2 a vertical paned containing
*)

let hp = GPack.paned `HORIZONTAL ~packing:hb#add ()

let scrollview =
  let sv =
    GBin.scrolled_window
      ~hpolicy:`AUTOMATIC ~vpolicy:`AUTOMATIC
      ~width:gconfig.tree_width ~shadow_type:`ETCHED_OUT
      ~packing:hp#add ()
  in
  let (_ : GtkSignal.id) =
    sv#misc#connect#size_allocate
      ~callback:
      (fun {Gtk.width=w;Gtk.height=_h} ->
       gconfig.tree_width <- w)
  in sv

let vpan222 = GPack.paned `VERTICAL ~packing:hp#add ()

(*  the scrolled window 2.2.1 contains a GTK tree

*)


(* view for the session tree *)
let scrolled_session_view =
  GBin.scrolled_window
    ~hpolicy: `AUTOMATIC ~vpolicy: `AUTOMATIC
    ~shadow_type:`ETCHED_OUT
    ~packing:scrollview#add
    ()

let cols = new GTree.column_list
let name_column = cols#add Gobject.Data.string
let index_column = cols#add Gobject.Data.int
let status_column = cols#add Gobject.Data.gobject

let name_renderer = GTree.cell_renderer_text [`XALIGN 0.]
let view_name_column = GTree.view_column ~title:"Theories/Goals" ()
let () =
  view_name_column#pack name_renderer;
  view_name_column#add_attribute name_renderer "text" name_column;
  view_name_column#set_sizing `AUTOSIZE

let status_renderer = GTree.cell_renderer_pixbuf [ ]
let view_status_column = GTree.view_column ~title:"Status"
    ~renderer:(status_renderer, ["pixbuf", status_column])()

let goals_model,goals_view =
  Debug.dprintf debug "[GUI] Creating tree model...@?";
  let model = GTree.tree_store cols in
  let view = GTree.view ~model ~packing:scrolled_session_view#add () in
(*
  let () = view#selection#set_mode (* `SINGLE *) `MULTIPLE in
  let () = view#set_rules_hint true in
 *)
  ignore (view#append_column view_name_column);
  ignore (view#append_column view_status_column);
(*
  ignore (view#append_column view_status_column);
  ignore (view#append_column view_time_column);
*)
  Debug.dprintf debug " done@.";
  model,view

(* vpan222 contains:
   2.2.2.1 a view of the current task
   2.2.2.2 a vertiacal pan which contains
     2.2.2.2.1 the input field to type commands
     2.2.2.2.2 a scrolled window to hold the output of the commands
 *)

let scrolled_task_view =
  GBin.scrolled_window
    ~hpolicy: `AUTOMATIC ~vpolicy: `AUTOMATIC
    ~shadow_type:`ETCHED_OUT
    ~packing:vpan222#add ()

let task_view =
  GSourceView2.source_view
    ~editable:false
    ~cursor_visible:false
    ~show_line_numbers:true
    ~packing:scrolled_task_view#add
    ()

let vbox2222 = GPack.vbox ~packing:vpan222#add  ()

let hbox22221 =
  GPack.hbox
    ~packing:(vbox2222#pack ?from:None ?expand:None ?fill:None ?padding:None) ()

let monitor =
  GMisc.label
    ~text:"  0/0/0"
    ~width:80
    ~xalign:0.0
    ~packing:(hbox22221#pack ?from:None ?expand:None ?fill:None ?padding:None) ()

let command_entry = GEdit.entry ~packing:hbox22221#add ()

let message_zone =
  let sv = GBin.scrolled_window
      ~hpolicy:`AUTOMATIC ~vpolicy:`AUTOMATIC
      ~shadow_type:`ETCHED_OUT ~packing:vbox2222#add ()
  in
  GText.view ~editable:false ~cursor_visible:false
    ~packing:sv#add ()

(**** Monitor *****)
(* TODO
let fan n =
  match n mod 4 with
    | 0 -> "|"
    | 1 | -3 -> "\\"
    | 2 | -2 -> "-"
    | 3 | -1 -> "/"
    | _ -> assert false

let update_monitor =
  let c = ref 0 in
  fun t s r ->
  reset_gc ();
  incr c;
  let f = if r=0 then "  " else fan (!c / 2) ^ " " in
  monitor#set_text
    (f ^ (string_of_int t) ^ "/" ^ (string_of_int s) ^ "/" ^ (string_of_int r))
*)

(****************************)
(* command entry completion *)
(****************************)

let completion_cols = new GTree.column_list
let completion_col = completion_cols#add Gobject.Data.string
(* let text_col = completion_cols#add Gobject.Data.string *)
let completion_model = GTree.tree_store completion_cols

let command_entry_completion : GEdit.entry_completion =
  GEdit.entry_completion ~model:completion_model ~minimum_key_length:1 ~entry:command_entry ()

let add_completion_entry s =
  let row = completion_model#append () in
  (* completion_model#set ~row ~column:text_col "test"; *)
  completion_model#set ~row ~column:completion_col s

let match_function s iter =
  let candidate = completion_model#get ~row:iter ~column:completion_col in
  try
    ignore (Str.search_forward (Str.regexp s) candidate 0);
    true
  with Not_found -> false

let init_comp () =
  (* add the names of all the the transformations *)
  List.iter add_completion_entry !transformation_list;
  (* add the name of the commands *)
(*  List.iter (fun (c,_,_) -> add_completion_entry c)
    !commands; (* TODO re-add commands *)*)
  (* todo: add queries *)

  (* add provers *)
  List.iter add_completion_entry !provers_list;
(*
  Whyconf.Hprover.iter
      (fun p _ -> add_completion_entry (p.Whyconf.prover_name^","^p.Whyconf.prover_version))
      cont.controller_provers;
*)
  add_completion_entry "auto";
  add_completion_entry "auto 2";

  command_entry_completion#set_text_column completion_col;
  command_entry_completion#set_match_func match_function;
(*  ignore (command_entry_completion#connect#match_selected
    ~callback:(fun _ iter ->
        command_entry#set_text "test";
        true));*)

    (* GTree.model_filter -> Gtk.tree_iter -> bool *)

  command_entry#set_completion command_entry_completion




(*********************)
(* Terminal historic *)
(*********************)

let list_commands = create_historic()

let _ =
  command_entry#event#connect#key_press
    ~callback:(fun (ev: 'a Gdk.event) ->
      match GdkEvent.Key.keyval ev with
      | k when k = GdkKeysyms._Up -> (* Arrow up *)
          let s = print_next_command list_commands in
          (match s with
          | None -> true
          | Some s ->
              (command_entry#set_text s; true))
      | k when k = GdkKeysyms._Down -> (* Arrow down *)
          let s = print_prev_command list_commands in
          (match s with
          | None -> true
          | Some s ->
              (command_entry#set_text s; true))
      | _ -> false
      )

(********************************************)
(* controller instance on the GTK scheduler *)
(********************************************)

(*
module S = struct
    let idle ~prio f =
      let (_ : GMain.Idle.id) = GMain.Idle.add ~prio f in ()

    let timeout ~ms f =
      let (_ : GMain.Timeout.id) = GMain.Timeout.add ~ms ~callback:f in
      ()
end

module C = Controller_itp.Make(S)
*)

let (_ : GtkSignal.id) =
  replay_menu_item#connect#activate
    ~callback:(fun () ->
               (*let callback = C.replay_print in*)
               P.send_request (Replay, ""))
(*C.replay ~use_steps:false cont ~callback ~remove_obsolete:false)*)

let tree = ref (Node ("", "", Root, {proved = false; name= ""}, []))

(***********************************)
(* Mapping session to the GTK tree *)
(***********************************)
(*
type index =
  | Inone
  | IproofAttempt of proofAttemptID
  | IproofNode of proofNodeID
  | Itransformation  of transID
  | Ifile of file
  | Itheory of theory

let model_index : index Hint.t = Stdlib.Hint.create 17
let get_index iter =
  let index = goals_model#get ~row:iter ~column:index_column in
  Hint.find model_index index

(* To each node we have the corresponding row_reference *)
let file_id_to_gtree : GTree.row_reference Hstr.t = Hstr.create 3
let th_id_to_gtree   : GTree.row_reference Ident.Hid.t = Ident.Hid.create 7
let pn_id_to_gtree   : GTree.row_reference Hpn.t = Hpn.create 17
let tn_id_to_gtree   : GTree.row_reference Htn.t = Htn.create 17
let pan_id_to_gtree  : GTree.row_reference Hpan.t = Hpan.create 17

(* TODO exception for those: *)
let row_from_file file = Hstr.find file_id_to_gtree (file.file_name)
let row_from_th   th   = Ident.Hid.find th_id_to_gtree (theory_name th)
let row_from_pn   pn   = Hpn.find pn_id_to_gtree pn
let row_from_tn   tn   = Htn.find tn_id_to_gtree tn
let row_from_pan  pan  = Hpan.find pan_id_to_gtree pan
*)

let model_node: node_ID Hint.t = Stdlib.Hint.create 17

let node_from_iter iter =
  let index = goals_model#get ~row:iter ~column:index_column in
  Hint.find model_node index

let iter_node: GTree.row_reference Hstr.t = Stdlib.Hstr.create 17

let row_ref_from_node node =
  Hstr.find iter_node node

let new_node =
  let cpt = ref (-1) in
  fun ?parent ?(collapse=false) name (ind: node_ID) ->
  incr cpt;
  Hint.add model_node !cpt ind;
  let parent = Opt.map (fun x -> x#iter) parent in
  let iter = goals_model#append ?parent () in
  goals_model#set ~row:iter ~column:name_column name;
  goals_model#set ~row:iter ~column:index_column !cpt;
  let new_ref = goals_model#get_row_reference (goals_model#get_path iter) in
  (* By default expand_path when creating a new node *)
  if not collapse then goals_view#expand_to_path (goals_model#get_path iter);
  begin
(* TODO reverse hashtable necessary ? *)
    (*
    match ind with
    | IproofAttempt panid ->
       Hpan.add pan_id_to_gtree panid new_ref
    | IproofNode pnid ->
      Hpn.add pn_id_to_gtree pnid new_ref
    | Itransformation tnid ->
      Htn.add tn_id_to_gtree tnid new_ref
    | Ifile file ->
      Hstr.add file_id_to_gtree file.file_name new_ref
    | Itheory th ->
      Ident.Hid.add th_id_to_gtree (theory_name th) new_ref
    | Inone -> ()
     *)
  end;
  new_ref


let image_of_result ~obsolete rOpt =
  match rOpt with
  | None -> !image_undone
  | Some r ->
    match r.Call_provers.pr_answer with
    | Call_provers.Valid ->
      if obsolete then !image_valid_obs else !image_valid
    | Call_provers.Invalid ->
      if obsolete then !image_invalid_obs else !image_invalid
    | Call_provers.Timeout ->
      if obsolete then !image_timeout_obs else !image_timeout
    | Call_provers.OutOfMemory ->
      if obsolete then !image_outofmemory_obs else !image_outofmemory
    | Call_provers.StepLimitExceeded ->
      if obsolete then !image_steplimitexceeded_obs
      else !image_steplimitexceeded
    | Call_provers.Unknown _ ->
      if obsolete then !image_unknown_obs else !image_unknown
    | Call_provers.Failure _ ->
      if obsolete then !image_failure_obs else !image_failure
    | Call_provers.HighFailure ->
      if obsolete then !image_failure_obs else !image_failure

let get_type_info (n: node_ID) (t: session_tree): node_type * node_info =
  (* TODO parcours du tree pour obtenir le type et l'info *)
  Obj.magic "TODO"

let set_status_column_from_cont iter =
  let node_ID = node_from_iter iter in
  let _, info = get_type_info node_ID !tree in
  let image =
    if info.proved then
      !image_valid
    else
      !image_unknown
  in
  goals_model#set ~row:iter ~column:status_column image

(*
let build_subtree_proof_attempt_from_goal cont row_ref id =
  Whyconf.Hprover.iter
    (fun pa panid ->
       let name = Pp.string_of Whyconf.print_prover pa in
       let r = new_node ~parent:row_ref name (IproofAttempt panid) in
       set_status_column_from_cont cont r#iter)
    (get_proof_attempt_ids cont.controller_session id)

let rec build_subtree_from_goal cont th_row_reference id =
  let ses = cont.controller_session in
  let name = get_proof_name ses id in
  let row_ref =
    new_node ~parent:th_row_reference name.Ident.id_string
             (IproofNode id)
  in
  set_status_column_from_cont cont row_ref#iter;
  List.iter
    (fun trans_id ->
      ignore (build_subtree_from_trans cont row_ref trans_id))
    (get_transformations ses id);
  build_subtree_proof_attempt_from_goal cont row_ref id

and build_subtree_from_trans cont goal_row_reference trans_id =
  let ses = cont.controller_session in
  let name = get_transf_name ses trans_id in
  let row_ref =
    new_node ~parent:goal_row_reference name (Itransformation trans_id) in
  set_status_column_from_cont cont row_ref#iter;
  List.iter
    (fun goal_id ->
      (build_subtree_from_goal cont row_ref goal_id))
    (get_sub_tasks ses trans_id);
  row_ref
*)

let rec build_tree_from_session ?parent (t: session_tree) =
  match t with
  | Node (node_ID, pos_ID, node_type, node_info, subtree_list) ->
    let row_ref = new_node ?parent:parent node_info.name node_ID in
    set_status_column_from_cont row_ref#iter;
    List.iter (build_tree_from_session ~parent:row_ref) subtree_list

(*
let build_tree_from_session cont =
  let ses = cont.controller_session in
  let files = get_files ses in
  Stdlib.Hstr.iter
    (fun _ file ->
       let file_row_reference = new_node file.file_name (Ifile file) in
       set_status_column_from_cont cont file_row_reference#iter;
       List.iter (fun th ->
                  let th_row_reference =
                    new_node ~parent:file_row_reference
                             (theory_name th).Ident.id_string
                             (Itheory th)
                  in
                  set_status_column_from_cont cont th_row_reference#iter;
                  List.iter (build_subtree_from_goal cont th_row_reference)
                            (theory_goals th))
                 file.file_theories)
    files
*)

(*******************************)
(* commands of the "View" menu *)
(*******************************)

let view_menu = factory#add_submenu "_View"
let view_factory = new GMenu.factory view_menu ~accel_group

(* goals view is not yet multi-selectable
let (_ : GMenu.image_menu_item) =
  view_factory#add_image_item ~key:GdkKeysyms._A
    ~label:"Select all"
    ~callback:(fun () -> goals_view#selection#select_all ()) ()
 *)

let (_ : GMenu.menu_item) =
  view_factory#add_item ~key:GdkKeysyms._plus
    ~callback:(fun _ -> enlarge_fonts gconfig) "Enlarge font"

let (_ : GMenu.menu_item) =
    view_factory#add_item ~key:GdkKeysyms._minus
      ~callback:(fun _ -> reduce_fonts gconfig) "Reduce font"

let (_ : GMenu.image_menu_item) =
  view_factory#add_image_item ~key:GdkKeysyms._E
    ~label:"Expand all" ~callback:(fun () -> goals_view#expand_all ()) ()

let collapse_iter iter =
  let path = goals_model#get_path iter in
  goals_view#collapse_row path

let get_node_row (n: node_ID) : GTree.row_reference = Obj.magic "TODO"

let rec collapse_proven_tree (tree: session_tree) =
  match tree with
  | Node (node_ID, pos_ID, node_type, node_info, subtree_list) ->
    if node_info.proved then
      let row = get_node_row node_ID in
      collapse_iter row#iter
    else
      List.iter collapse_proven_tree subtree_list

(* TODO to remove
let rec collapse_proven_goals_from_pn pn =
  match pn_proved cont pn with
  | true  -> collapse_iter (row_from_pn pn)#iter
  | false ->
    List.iter collapse_proven_goals_from_tn
      (get_transformations cont.controller_session pn)

and collapse_proven_goals_from_tn tn =
  match tn_proved cont tn with
  | true  -> collapse_iter (row_from_tn tn)#iter
  | false ->
    List.iter collapse_proven_goals_from_pn
      (get_sub_tasks cont.controller_session tn)

let collapse_proven_goals_from_th th =
  match th_proved cont th with
  | true  -> collapse_iter (row_from_th th)#iter
  | false -> List.iter collapse_proven_goals_from_pn (theory_goals th)

let collapse_proven_goals_from_file file =
  match file_proved cont file with
  | true  -> collapse_iter (row_from_file file)#iter
  | false -> List.iter collapse_proven_goals_from_th file.file_theories

let collapse_proven_goals_from_iter iter =
  let index = get_index iter in
  match index with
  | Inone              -> assert false
  | IproofAttempt _    -> ()
  | IproofNode pn      -> collapse_proven_goals_from_pn pn
  | Itransformation tn -> collapse_proven_goals_from_tn tn
  | Itheory th         -> collapse_proven_goals_from_th th
  | Ifile file         -> collapse_proven_goals_from_file file

let collapse_proven_goals () =
  match goals_model#get_iter_first with
  | None -> ()
  | Some root_iter -> collapse_proven_goals_from_iter root_iter
*)

let (_ : GMenu.image_menu_item) =
  view_factory#add_image_item ~key:GdkKeysyms._C
    ~label:"Collapse proven goals" ~callback:(fun () -> collapse_proven_tree !tree) ()

let () =
  Gconfig.add_modifiable_sans_font_view goals_view#misc;
  Gconfig.add_modifiable_mono_font_view monitor#misc;
  Gconfig.add_modifiable_mono_font_view task_view#misc;
  Gconfig.add_modifiable_mono_font_view command_entry#misc;
  Gconfig.add_modifiable_mono_font_view message_zone#misc;
  task_view#source_buffer#set_language why_lang;
  Gconfig.set_fonts gconfig

(******************)
(*    actions     *)
(******************)

(* TODO We currently use this for transformations etc... With strategies, we sure
   do not want to move the current index with the computing of strategy. *)
let current_selected_index = ref ""

let image_of_pa_status ~obsolete pa_status =
  match pa_status with
    | Controller_itp.Interrupted   -> !image_undone
    | Controller_itp.Unedited      -> !image_editor
    | Controller_itp.JustEdited    -> !image_unknown
    | Controller_itp.Scheduled     -> !image_scheduled
    | Controller_itp.Running       -> !image_running
    | Controller_itp.InternalFailure _
    | Controller_itp.Uninstalled _ -> !image_failure
    | Controller_itp.Done r        -> image_of_result ~obsolete (Some r)

let rec update_status_column_from_iter cont iter =
  set_status_column_from_cont iter;
  match goals_model#iter_parent iter with
  | Some p -> update_status_column_from_iter cont p
  | None -> ()

let move_current_row_selection_up () =
  let current_view = List.hd (goals_view#selection#get_selected_rows) in
  ignore (GTree.Path.up current_view);
  let row_up = goals_model#get_row_reference current_view in
  goals_view#selection#select_iter row_up#iter

let move_current_row_selection_down () =
  let current_iter =
    try
      let current_view = List.hd (goals_view#selection#get_selected_rows) in
      let current_row = goals_model#get_row_reference current_view in
      Some current_row#iter
    with Not_found ->
      None
  in
  let child = goals_model#iter_children current_iter in
  goals_view#selection#select_iter child

(* Callback of a transformation *)
(*
let callback_update_tree_transform cont status =
  match status with
  | TSdone trans_id ->
    let ses = cont.controller_session in
    let id = get_trans_parent ses trans_id in
    let row_ref = row_from_pn id in
    let r = build_subtree_from_trans cont row_ref trans_id in
    update_status_column_from_iter cont r#iter;
    (* move focus if the current index still corresponds to the
       goal *)
    let ppn = get_trans_parent cont.controller_session trans_id in
    begin match !current_selected_index with
      | IproofNode pn when pn = ppn ->
        (match Session_itp.get_sub_tasks ses trans_id with
         | first_goal :: _ ->
           (* Put the selection on the first goal *)
           goals_view#selection#select_iter (row_from_pn first_goal)#iter
         | [] -> ())
      | _ -> ()
    end;
  | TSfailed (id, e) ->
      message_zone#buffer#set_text
        (Pp.sprintf "%a" (get_exception_message cont.controller_session id) e)
  | _ -> ()
*)

(*
let rec apply_transform cont t args =
  match !current_selected_index with
  | IproofNode id ->
     let callback = callback_update_tree_transform cont in
     C.schedule_transformation cont id t args ~callback
  | IproofAttempt _ ->
    move_current_row_selection_up ();
    apply_transform cont t args
  | Itransformation _ | Ifile _ | Itheory _ | Inone ->
    begin try move_current_row_selection_down () with
      Not_found -> printf "no goals to apply transform"
    end;
    apply_transform cont t args
*)

(* TODO this is from tree to tree *)
(* TODO do this later
let go_to_nearest_unproven_goal_and_collapse (t: session_tree) =
  match t with
  | Node (node_ID, pos_ID, node_type, node_info, subtree_list) ->
    match node_type with
    |
*)
(*
  begin match get_first_unproven_goal_around_pn cont pn with
    | Some next_pn ->
      goals_view#selection#select_iter (row_from_pn next_pn)#iter
    | None -> ()
  end;
  collapse_proven_goals ()
*)

(* Callback of a proof_attempt *)
(*
let callback_update_tree_proof cont panid pa_status =
  let ses = cont.controller_session in
  let pa = get_proof_attempt_node ses panid in
  let prover = pa.prover in
  let name = Pp.string_of Whyconf.print_prover prover in
  let obsolete = pa.proof_obsolete in
  let r = match pa_status with
    | Scheduled ->
      begin
        try row_from_pan panid
        with Not_found ->
          let parent_id = get_proof_attempt_parent ses panid in
          let parent = row_from_pn parent_id in
          new_node ~parent name (IproofAttempt panid)
      end
    | Done _ ->
      let ppn = get_proof_attempt_parent cont.controller_session panid in
      let piter = (row_from_pn ppn)#iter in
      update_status_column_from_iter cont piter;
      (* move focus an collapse if the goal was proven and
         the current index still corresponds to the goal *)
      begin match !current_selected_index with
        | IproofNode pn when pn = ppn ->
          if pn_proved cont pn then
            go_to_nearest_unproven_goal_and_collapse pn
        | _ -> ()
      end;
      row_from_pan panid
    | _  -> row_from_pan panid (* TODO ? *)
  in
  goals_model#set ~row:r#iter ~column:status_column
    (image_of_pa_status ~obsolete pa_status)
*)

(*
let test_schedule_proof_attempt cont (p: Whyconf.config_prover) limit =
  let prover = p.Whyconf.prover in
  let callback = callback_update_tree_proof cont in
  let rec get_goals () =
    match !current_selected_index with
    | IproofNode id -> [id]
    | IproofAttempt _ ->
      move_current_row_selection_up ();
      get_goals ()
    | Itransformation tn ->
      List.rev (unproven_goals_below_tn cont [] tn)
    | Ifile file ->
      List.rev (unproven_goals_below_file cont file)
    | Itheory th ->
      List.rev (unproven_goals_below_th cont [] th)
    | Inone -> []
  in
  List.iter (fun id -> C.schedule_proof_attempt cont id prover ~limit ~callback)
    (get_goals ())
*)

(*
let run_strategy_on_task s =
  match !current_selected_index with
  | IproofNode id ->
     let l = Session_user_interface.strategies
               cont.controller_env gconfig.config
     in
     let st = List.filter (fun (_,c,_,_) -> c=s) l in
     begin
       match st with
       | [(n,_,_,st)] ->
          printf "running strategy '%s'@." n;
          let callback sts =
            printf "Strategy status: %a@." print_strategy_status sts
          in
          let callback_pa =
            callback_update_tree_proof cont
          in
          let callback_tr st =
            callback_update_tree_transform cont st
          in
          C.run_strategy_on_goal cont id st ~callback_pa ~callback_tr ~callback
    | _ -> printf "Strategy '%s' not found@." s
     end
  | _ -> ()
*)

let clear_command_entry () = command_entry#set_text ""

let current_node_ID () = !current_selected_index


(* TODO now split as notifications and inside session_user_interface
let interp cmd =
  let id =
    match !current_selected_index with
    | IproofNode id -> Some id
    | _ -> None
  in
  try
  match interp cont id cmd with
    | Transform(s,_t,args) ->
       clear_command_entry ();
       apply_transform cont s args
    | Query s ->
       clear_command_entry ();
       message_zone#buffer#set_text s
    | Other(s,args) ->
      begin
        match parse_prover_name gconfig.config s args with
        | Some (prover_config, limit) ->
          clear_command_entry ();
          test_schedule_proof_attempt cont prover_config limit
        | None ->
          match s with
          | "auto" ->
             let s =
               match args with
               | "2"::_ -> "2"
               | _ -> "1"
             in
             clear_command_entry ();
             run_strategy_on_task s
          | "help" ->
             clear_command_entry ();
             let text = Pp.sprintf
                          "Please type a command among the following (automatic completion available)@\n\
                           @\n\
                           @ <transformation name> [arguments]@\n\
                           @ <prover name> [<time limit> [<mem limit>]]@\n\
                           @ <query> [arguments]@\n\
                           @ auto [auto level]@\n\
                           @\n\
                           Available queries are:@\n@[%a@]" help_on_queries ()
             in
             message_zone#buffer#set_text text
          | _ ->
             message_zone#buffer#set_text ("unknown command '"^s^"'")
      end
  with e when not (Debug.test_flag Debug.stack_trace) ->
       message_zone#buffer#set_text (Pp.sprintf "anomaly: %a" Exn_printer.exn_printer e)
*)

let (_ : GtkSignal.id) =
  command_entry#connect#activate
    ~callback:(fun () ->
      add_command list_commands command_entry#text;
      let node_ID = current_node_ID () in
      P.send_request (Command command_entry#text, node_ID))


let get_selected_row_references () =
  List.map
    (fun path -> goals_model#get_row_reference path)
    goals_view#selection#get_selected_rows

(* TODO we now change it when notify
let on_selected_row r =
  try
    let session_element = get_index r#iter in
    current_selected_index := session_element;
    match session_element with
    | IproofNode id ->
       let task = get_task cont.controller_session id in
       let tables = get_tables cont.controller_session id in
       let s = Pp.string_of
                 (fun fmt -> Driver.print_task ~cntexample:false task_driver fmt tables)
                 task
       in task_view#source_buffer#set_text s;
       (* scroll to end of text *)
       task_view#scroll_to_mark `INSERT
    | _ -> task_view#source_buffer#set_text ""
  with
    | Not_found -> task_view#source_buffer#set_text ""
*)
(*
let (_ : GtkSignal.id) =
  goals_view#selection#connect#after#changed ~callback:
    (fun () ->
      match get_selected_row_references () with
        | [r] -> on_selected_row r
        | _ -> ())
*)

(***********************)
(* start the interface *)
(***********************)

(* TODO after init this *)
let init () =
  build_tree_from_session !tree;
  (* temporary *)
  init_comp ();
  vpan222#set_position 500;
  goals_view#expand_all ();
  main_window#add_accel_group accel_group;
  main_window#set_icon (Some !Gconfig.why_icon);
  message_zone#buffer#set_text "Welcome to Why3 IDE\ntype 'help' for help";
  main_window#show ();
  GMain.main ()

exception Bad_initialization


exception Disynchronized

let change_row iter node_info : unit =
  goals_model#set ~row:iter ~column:name_column node_info.name;
  set_status_column_from_cont iter
(*  goals_model#set ~row:iter ~column:status_column image*)

(* TODO bad style on update_node functions *)
let rec update_node genealogy node_ID node_info tree =
  match tree, genealogy with
  | Node (cur_node_ID, cur_pos_ID, nt, ni, subtree_list), [] when cur_node_ID = node_ID ->
    (let n = Node (cur_node_ID, cur_pos_ID, nt, node_info, subtree_list) in
     let row = row_ref_from_node cur_node_ID in
     change_row row#iter node_info;
     n)
  | Node (cur_node_ID, cur_pos_ID, nt, ni, subtree_list), [] when cur_node_ID != node_ID ->
    (P.send_request (Get_Session_Tree, ""); raise Disynchronized)
  | Node (cur_node_ID, cur_pos_ID, nt, ni, subtree_list), hd :: tl when hd != cur_pos_ID ->
    Node (cur_node_ID, cur_pos_ID, nt, ni, subtree_list) (* TODO raise failed *)
  | Node (cur_node_ID, cur_pos_ID, nt, ni, subtree_list), hd :: tl when hd = cur_pos_ID ->
    Node (cur_node_ID, cur_pos_ID, nt, ni,
          List.map (update_node tl node_ID node_info) subtree_list)
  | t, _ -> t

let rec update_subtree genealogy node_ID subtree tree =
  match tree, genealogy with
  | Node (cur_node_ID, cur_pos_ID, nt, ni, subtree_list), [] when cur_node_ID = node_ID ->
      Node (cur_node_ID, cur_pos_ID, nt, ni, subtree :: subtree_list)
        (* TODO add side effect on goal view *)
  | Node (cur_node_ID, cur_pos_ID, nt, ni, subtree_list), [] when cur_node_ID != node_ID ->
    (P.send_request (Get_Session_Tree, ""); raise Disynchronized)
  | Node (cur_node_ID, cur_pos_ID, nt, ni, subtree_list), hd :: tl when hd != cur_pos_ID ->
    Node (cur_node_ID, cur_pos_ID, nt, ni, subtree_list) (* TODO raise failed *)
  | Node (cur_node_ID, cur_pos_ID, nt, ni, subtree_list), hd :: tl when hd = cur_pos_ID ->
    Node (cur_node_ID, cur_pos_ID, nt, ni,
          List.map (update_subtree tl node_ID subtree) subtree_list)
  | t, _ -> t

let update_tree notification =
  match notification with
  | Node_change (node_ID, node_info) ->
    let genealogy = Str.split (Str.regexp ".") node_ID in
    (try tree := update_node genealogy node_ID node_info !tree with
    | Disynchronized -> ())
  | Session_Tree (session_tree) ->
    tree := session_tree
  | New_subtree (nid, subtree) ->
    let genealogy = Str.split (Str.regexp ".") nid in
    (try tree := update_subtree genealogy nid subtree !tree with
    | Disynchronized -> ())
  | _ -> ()


let rec treat_notifs l =
  if !is_init then
    match l with
    | [] -> ()
    | Initialized _ :: tl ->
      raise Bad_initialization
    | Node_change (nid, node_info) :: tl ->
      update_tree (Node_change (nid, node_info));
      treat_notifs tl
    | New_subtree (nid, subtree) :: tl ->
      update_tree (New_subtree (nid, subtree));
      treat_notifs tl
    | Saved :: tl -> treat_notifs tl
    | Remove nid :: tl -> update_tree (Remove nid); treat_notifs tl
    | Error e :: tl -> failwith "TODO implement errors"
    | Message s :: tl -> failwith "TODO implemenbt this"
    | Session_Tree t :: tl -> update_tree (Session_Tree t)
  else
    match l with
    | [] -> ()
    | Initialized (infos, pl, trl, sl) :: tl ->
      begin
        try
          (provers_list := pl;
           transformation_list := trl;
           strategy_list := sl;
           is_init := true;
           let nc = Gconfig.load_config infos in
           Gconfig.config gconfig nc;
           Debug.dprintf debug "[GUI] Init the GTK interface...@?";
           ignore (GtkMain.Main.init ());
           Debug.dprintf debug " done.@.";
           Gconfig.init gconfig infos.main_dir;
           main_dir := infos.main_dir;
           treat_notifs tl
          )
        with e when not (Debug.test_flag Debug.stack_trace) ->
          Format.eprintf "%a@." Exn_printer.exn_printer e;
          exit 1
      end
    | _ :: tl -> treat_notifs tl


let treat_notifications () : bool =
  let l = P.get_notified () in
  treat_notifs l;
  true

  let _ = Unix_scheduler.Unix_Scheduler.idle ~prio:1 treat_notifications

end

module IDE = Make (Protocol.Protocol_why3ide)
