theory Tools
  imports ML_Environment
begin

text\<open>Based on @{file "../HOL/tools/Holmake/poly/poly-Holmake.ML"}\<close>

declare [[ML_environment = "HOL4"]]
(*
ML \<open>Context_Var.bind_ref "HOL4_Tools"\<close>*)


text\<open>Im copy and pasting because its kinda easier to maintain since there are clear files this
stuff is based on
\<close>
text\<open>Based on @{file "../HOL/tools-poly/poly/poly-init.ML"}\<close>
subsection \<open>poly-init.ML\<close>

ML_file \<open>../HOL/tools-poly/poly/Mosml.sml\<close>
ML_file \<open>../HOL/tools-poly/poly/Binarymap.sig\<close>
ML_file \<open>../HOL/tools-poly/poly/Binarymap.sml\<close>
ML_file \<open>../HOL/tools-poly/poly/Binaryset.sig\<close>
ML_file \<open>../HOL/tools-poly/poly/Binaryset.sml\<close>
ML_file \<open>../HOL/tools-poly/poly/Listsort.sig\<close>
ML_file \<open>../HOL/tools-poly/poly/Listsort.sml\<close>
ML_file \<open>../HOL/tools/Holmake/holpathdb.sig\<close>
ML_file \<open>../HOL/tools/Holmake/holpathdb.sml\<close>
external_file \<open>../HOL/tools-poly/Holmake/CompilerSpecific.ML\<close>
ML \<open>structure CompilerSpecific :>
  sig
    val quietbind : string -> unit
  end =
struct

fun quietbind s =
  ML_Compiler.eval {debug = NONE, environment="HOL4", redirect = false, verbose = false, catch_all = true,
  warning = fn _ => (), writeln = fn _ => ()} Position.none (ML_Lex.tokenize s)
end\<close>
ML_file \<open>../HOL/tools/Holmake/Systeml.sig\<close>
ML_file \<open>../HOL/tools-poly/Holmake/Systeml.sml\<close>

text\<open>Based on @{file "../HOL/tools/Holmake/hmcore.ML"}\<close>
ML_file \<open>../HOL/tools/Holmake/HOLFS_dtype.sml\<close>
ML_file \<open>../HOL/tools/Holmake/HFS_NameMunge.sig\<close>
ML_file \<open>../HOL/tools/Holmake/poly/HFS_NameMunge.sml\<close>
ML_file \<open>../HOL/tools/Holmake/HOLFileSys.sig\<close>
ML_file \<open>../HOL/tools/Holmake/HOLFileSys.sml\<close>
ML_file \<open>../HOL/tools/Holmake/regexpMatch.sig\<close>
ML_file \<open>../HOL/tools/Holmake/regexpMatch.sml\<close>
ML_file \<open>../HOL/tools/Holmake/parse_glob.sig\<close>
ML_file \<open>../HOL/tools/Holmake/parse_glob.sml\<close>
ML_file \<open>../HOL/tools/Holmake/Holdep_tokens.sig\<close>
ML_file \<open>../HOL/tools/Holmake/Holdep_tokens.sml\<close>
ML_file \<open>../HOL/tools/Holmake/AttributeSyntax.sig\<close>
ML_file \<open>../HOL/tools/Holmake/AttributeSyntax.sml\<close>
ML_file \<open>../HOL/tools/Holmake/QuoteFilter.sml\<close>
ML_file \<open>../HOL/tools/Holmake/Holmake_tools_dtype.sml\<close>
ML_file \<open>../HOL/tools/Holmake/terminal_primitives.sig\<close>
external_file \<open>../HOL/tools/Holmake/poly-terminal-prims.ML\<close>
ML\<open>
structure terminal_primitives :> terminal_primitives =
struct
(*TODO figure out what this is for*)
fun strmIsTTY (outstream : TextIO.outstream) = false

fun TERM_isANSI () = false

end\<close>
ML_file \<open>../HOL/tools/Holmake/QFRead.sig\<close>
ML_file \<open>../HOL/tools/Holmake/QFRead.sml\<close>
ML_file \<open>../HOL/tools/Holmake/Holdep.sig\<close>
ML_file \<open>../HOL/tools/Holmake/Holdep.sml\<close>
ML_file \<open>../HOL/tools/Holmake/Holmake_tools.sig\<close>
ML_file \<open>../HOL/tools/Holmake/Holmake_tools.sml\<close>
ML \<open>structure Holmake_tools : Holmake_tools = struct
  open Holmake_tools
  fun getWidth () = 80
end\<close>
ML_file \<open>../HOL/tools/Holmake/internal_functions.sig\<close>
ML_file \<open>../HOL/tools/Holmake/internal_functions.sml\<close>
ML_file \<open>../HOL/tools/Holmake/Holmake_types.sig\<close>
ML_file \<open>../HOL/tools/Holmake/Holmake_types.sml\<close>
ML_file \<open>../HOL/tools/Holmake/ReadHMF.sig\<close>
ML_file \<open>../HOL/tools/Holmake/ReadHMF.sml\<close>





ML_file \<open>../HOL/tools/Holmake/tailbuffer.sig\<close>
ML_file \<open>../HOL/tools/Holmake/tailbuffer.sml\<close>
ML_file \<open>../HOL/tools/Holmake/GetOpt.sig\<close>
ML_file \<open>../HOL/tools/Holmake/GetOpt.sml\<close>
ML_file \<open>../HOL/tools/Holmake/FunctionalRecordUpdate.sml\<close>
ML_file \<open>../HOL/tools/Holmake/HM_Core_Cline.sig\<close>
ML_file \<open>../HOL/tools/Holmake/HM_Core_Cline.sml\<close>
ML_file \<open>../HOL/tools/Holmake/HM_DepGraph.sig\<close>
ML_file \<open>../HOL/tools/Holmake/HM_DepGraph.sml\<close>
ML_file \<open>../HOL/tools/Holmake/HM_GraphBuildJ1.sig\<close>
ML_file \<open>../HOL/tools/Holmake/HM_GraphBuildJ1.sml\<close>
ML_file \<open>../HOL/tools/Holmake/poly/HM_Cline.sig\<close>
ML_file \<open>../HOL/tools/Holmake/poly/HM_Cline.sml\<close>
ML_file \<open>../HOL/tools/Holmake/poly/GraphExtra.sig\<close>
ML_file \<open>../HOL/tools/Holmake/poly/GraphExtra.sml\<close>
ML_file \<open>../HOL/tools/Holmake/poly/HM_BaseEnv.sig\<close>
ML_file \<open>../HOL/tools/Holmake/poly/HM_BaseEnv.sml\<close>
ML_file \<open>../HOL/tools/Holmake/BuildCommand.sig\<close>
external_file \<open>../HOL/tools/Holmake/poly/ProcessMultiplexor.sig\<close>
external_file \<open>../HOL/tools/Holmake/poly/ProcessMultiplexor.sml\<close>

external_file \<open>../HOL/tools/Holmake/poly/MB_Monitor.sig\<close>
external_file \<open>../HOL/tools/Holmake/poly/MB_Monitor.sml\<close>
external_file \<open>../HOL/tools/Holmake/poly/multibuild.sml\<close>
ML \<open>structure BuildCommand :> BuildCommand =
struct

open Systeml Holmake_tools Holmake_types
structure FileSys = HOLFileSys
structure Path = OS.Path
structure Process = OS.Process

infix ++
fun p1 ++ p2 = Path.concat(p1,p2)
val SIGOBJ = Systeml.HOLDIR ++ "sigobj"



infix |>
fun x |> f = f x

val default_holstate = Systeml.DEFAULT_STATE

val _ = holpathdb.extend_db {vname = "HOLDIR", path = Systeml.HOLDIR}

open HM_GraphBuildJ1

datatype cmd_line = Mosml_compile of string list * string
                  | Mosml_link of string * string list
                  | Mosml_error
(*copied from multibuild*)
(*datatype buildresult = datatype multibuild.buildresult*)


datatype buildresult =
         BR_OK
       | BR_ClineK of { cline : string * string list,
                        job_kont : (string -> unit) -> OS.Process.status ->
                                   bool,
                        other_nodes : HM_DepGraph.node list }
       | BR_Failed

fun process_mosml_args (outs:Holmake_tools.output_functions) c = let
  val {diag,...} = outs
  val diag = fn s => diag "mosml_args" (fn _ => s)
  fun isSource t = OS.Path.ext t = SOME "sig" orelse OS.Path.ext t = SOME "sml"
  fun isObj t = OS.Path.ext t = SOME "uo" orelse OS.Path.ext t = SOME "ui"
  val toks = String.tokens (fn c => c = #" ") c
  val c = ref false
  val q = ref false
  val obj = ref NONE
  val I = ref []
  val obj_files = ref ([] : string list)
  val src_file = ref NONE
  fun process_args [] = ()
    | process_args ("-c"::rest) = (c := true; process_args rest)
    | process_args ("-q"::rest) = process_args rest
    | process_args ("-toplevel"::rest) = process_args rest
    | process_args ("-o"::arg::rest) = (obj := SOME arg; process_args rest)
    | process_args ("-I"::arg::rest) = (I := arg::(!I); process_args rest)
    | process_args (file::rest) = let
      in
        if file = HM_BaseEnv.mosml_indicator then ()
        else if isSource file then
          src_file := SOME file
        else if isObj file then
          obj_files := file :: !obj_files
        else ();
        process_args rest
      end
in
  process_args toks;
  ((case (!c, !src_file, !obj_files, !obj) of
         (true, SOME f, ofs, NONE) => Mosml_compile (List.rev ofs, f)
       | (false, NONE, ofs, SOME f) => Mosml_link (f, List.rev ofs)
       | _ => let
           fun ostring NONE = "NONE"
             | ostring (SOME s) = "SOME "^s
         in
           diag ("mosml error: c = "^Bool.toString (!c)^", src_file = "^
                 ostring (!src_file) ^ ", obj = "^ostring (!obj));
           Mosml_error
         end),
   List.rev (!I))
end;




fun posix_diagnostic stat = error "BuildCommand.posix_diagnostic"

fun addPath incs (file : string) : dep =
    let
      val dir = FileSys.getDir()
      open hm_target
    in
      if OS.Path.dir file <> "" then filestr_to_tgt file
      else let
        val p = List.find (fn p =>
                              FileSys.access (p ++ (file ^ ".ui"), []))
                          (dir :: incs)
      in
        case p of
            NONE => mk(hmdir.curdir(), toFile file)
          | SOME p => mk(hmdir.fromPath {origin = dir, path = p}, toFile file)
      end
    end

fun time_max(t1,t2) = if Time.<(t1,t2) then t2 else t1

fun finish_compilation warn depMods0 filename tgt =
  case OS.Process.getEnv Systeml.build_after_reloc_envvar of
      NONE => OS.Process.success
    | SOME "1" =>
      let
        val filename_base = OS.Path.base filename
        val depMods = List.filter (fn s => s <> filename_base) depMods0
        fun getFTime fname =
          SOME (FileSys.modTime fname) handle OS.SysErr _ => NONE
        fun combine fname t =
          case getFTime fname of NONE => t | SOME t0 => time_max(t0,t)
        fun foldthis (modn, t) =
          t |> combine (modn ^ ".uo") |> combine (modn ^ ".ui")
        val startTime =
            case getFTime filename of
                NONE => (warn("Can't see base file " ^ filename ^
                              " though I just compiled it??");
                         Time.zeroTime)
              | SOME t => t
      in
        FileSys.setTime (tgt, SOME (List.foldl foldthis startTime depMods));
        OS.Process.success
      end
    | SOME s =>
      (warn ("Ignoring strange value (" ^ s ^ ") in " ^
             Systeml.build_after_reloc_envvar ^ " environment variable");
       OS.Process.success)

fun poly_compile warn diag quietp file I (deps : dep list) objs = let
  open hm_target
  val _ = diag (fn _ => "poly-compiling " ^ fromFile file ^ "\n  deps = [" ^
                        concatWithf tgt_toString ", " deps ^ "]\n  objs = [" ^
                        String.concatWith ", " objs ^ "]")
  val modName = fromFileNoSuf file
  val deps = let
    open Binaryset
    val dep_set0 = addList (empty_tgtset, deps)
    val {deps = extra_deps, ...} =
        Holdep.main {assumes = [], includes = I, diag = diag,
                     fname = fromFile file}
    val dep_set =
        addList (dep_set0, map filestr_to_tgt extra_deps)
  in
    listItems dep_set
  end
  val depfiles = map (toFile o tgt_toString) deps
  val objfiles = map toFile objs
  fun mapthis (Unhandled _) = NONE
    | mapthis (DAT _) = NONE
    | mapthis f = SOME (fromFileNoSuf f)
  val depMods = List.mapPartial mapthis depfiles
  val objMods = List.map (addPath I) (List.mapPartial mapthis objfiles)
  fun usePathVars p = holpathdb.reverse_lookup {path = p}
  val depMods = List.map usePathVars (depMods @ map tgt_toString objMods)
  val say = if quietp then (fn s => ())
            else (fn s => FileSys.output(FileSys.stdOut, s ^ "\n"))
  val _ = say ("HOLMOSMLC -c " ^ fromFile file)
  val filename = tgt_toString (filestr_to_tgt (fromFile file))
  val _ = diag (fn _ => "Writing target with dependencies: " ^
                        String.concatWith ", " depMods)
in
case file of
  SIG _ =>
    (let
      val tgt = modName ^ ".ui"
      val outUi = FileSys.openOut tgt
     in
       FileSys.output (outUi, String.concatWith "\n" depMods);
       FileSys.output (outUi, "\n");
       FileSys.output (outUi, usePathVars filename ^ "\n");
       FileSys.closeOut outUi;
       finish_compilation warn depMods filename tgt
     end
     handle IO.Io _ => OS.Process.failure)
| SML _ =>
    (let
      val tgt = modName ^ ".uo"
      val outUo = FileSys.openOut tgt
     in
       FileSys.output (outUo, String.concatWith "\n" depMods);
       FileSys.output (outUo, "\n");
       FileSys.output (outUo, usePathVars filename ^ "\n");
       FileSys.closeOut outUo;
       (if FileSys.access (modName ^ ".sig", []) then
          ()
        else
          let val outUi = FileSys.openOut (modName ^ ".ui")
          in
            FileSys.closeOut outUi;
            ignore (finish_compilation warn depMods filename (modName ^ ".ui"))
          end);
       finish_compilation warn depMods filename tgt
     end
     handle IO.Io _ => OS.Process.failure)
| _ => raise Match
end

fun list_delete x [] = []
  | list_delete x (y::ys) = if x = y then ys else y :: list_delete x ys

type 'a build_command = 'a HM_DepGraph.t ->
                        {preincludes : string list, includes : string list} ->
                        (dep,'a) Holmake_tools.buildcmds ->
                        File -> bool

fun make_build_command (buildinfo : HM_Cline.t buildinfo_t) = let
  val {optv,actual_overlay,envlist,quit_on_failure,outs,...} =
      buildinfo
  val hmenv = #hmenv buildinfo
  val {warn,diag,tgtfatal,...} = outs
  val keep_going = #keep_going (#core optv)
  val debug = #debug (#core optv)
  val opentheory = #opentheory (#core optv)
  val allfast = #fast (#core optv)
  val polynothol = #poly_not_hol optv
  val relocbuild = #relocbuild optv orelse
                   (case OS.Process.getEnv Systeml.build_after_reloc_envvar of
                        SOME "1" => true
                      | _ => false)
  val interactive_flag = #interactive (#core optv)
  val quiet_flag = #quiet (#core optv)
  val cmdl_HOLSTATE = #holstate optv
  val jobs = #jobs (#core optv)
  val time_limit = #time_limit optv
  val chatty = if jobs = 1 then #chatty outs else (fn _ => ())
  val info = if jobs = 1 then #info outs else (fn _ => ())

  fun extra_poly_cline() = envlist "POLY_CLINE_OPTIONS"

  fun poly_link quietp extra result files =
  let
    open hm_target
    val _ = if not quietp then
              FileSys.output(FileSys.stdOut,
                             "HOLMOSMLC -o " ^ result ^ " " ^
                             String.concatWith " "
                                               (map (fn s => s ^ ".uo") files) ^
                             "\n")
            else ()
    val out = FileSys.openOut result
    fun p s =
        (FileSys.output (out, s); FileSys.output (out, "\n"))
  in
    p "#!/bin/sh";
    p ("set -e");
    p (protect(fullPath [HOLDIR, "bin", "buildheap"]) ^ " --gcthreads=1 " ^
       (case #holheap extra of NONE => "--poly"
                             | SOME d => "--holstate="^tgt_toString d) ^ " " ^
       (if isSome debug then "--dbg " else "") ^
       String.concatWith " " (extra_poly_cline()) ^ " " ^
       String.concatWith " " (map protect files));
    p ("exit 0");
    FileSys.closeOut out;
    Systeml.mk_xable result;
    OS.Process.success
  end handle IO.Io _ => OS.Process.failure

  fun build_command g (ii as {preincludes,includes}) c arg = let
    val diag = diag "build_command"
    val _ = diag (fn _ => "build_command on "^fromFile arg)
    val include_flags = preincludes @ includes
    val overlay_stringl = case actual_overlay of NONE => [] | SOME s => [s]
    exception CompileFailed
    exception FileNotFound
    val isSuccess = OS.Process.isSuccess
    fun setup_script s depinfo extras = let
      val scriptsml_file = SML (Script s)
      val scriptsml = fromFile scriptsml_file
      val script   = s^"Script"
      val scriptuo = script^".uo"
      val scriptui = script^".ui"
      (* first thing to do is to create the Script.uo file *)
      val b =
          case build_command g ii (Compile depinfo) scriptsml_file of
              BR_OK => true
            | BR_Failed => false
            | BR_ClineK _ => raise Fail "Compilation resulted in commandline"
      val _ = b orelse raise CompileFailed
      val _ = info ("Linking "^scriptuo^" to produce theory-builder executable")
      val objectfiles0 =
          if allfast then ["fastbuild.uo", scriptuo]
          else if quit_on_failure then [scriptuo]
          else ["holmakebuild.uo", scriptuo]
      val objectfiles0 = extras @ objectfiles0
      val objectfiles =
        if polynothol then
          objectfiles0
        else if interactive_flag then
          (SIGOBJ ++ "holmake_interactive.uo") :: objectfiles0
        else (SIGOBJ ++ "holmake_not_interactive.uo") :: objectfiles0
    in
        ((script,[scriptuo,scriptui,script]), objectfiles)
    end
    fun run_script g (extra:GraphExtra.t) (script, intermediates) objectfiles expecteds =
      let
        fun safedelete s = FileSys.remove s handle OS.SysErr _ => ()
        val _ = app safedelete expecteds
        val useScript = fullPath [HOLDIR, "bin", "buildheap"]
        val cline =
            useScript::"--gcthreads=1"::
            (case #multithread optv of
                 NONE => []
               | SOME i => ["--mt=" ^ Int.toString i]) @
            (case #holheap extra of NONE => "--poly"
                                  | SOME d => "--holstate="^tgt_toString d) ::
            extra_poly_cline() @
            ((if isSome debug then ["--dbg"] else []) @ objectfiles) @
            ["-e",
             "  check that export_theory call exists, and that new_theory\n\
             \  call is of the right name"] @
            List.concat (map (fn f => ["-c", f]) expecteds)
        fun cont wn res =
          let
            val _ =
                if not (isSuccess res) then
                  wn ("Failed script build for "^script^" - "^
                      posix_diagnostic res)
                else ()
            val _ = if isSuccess res orelse debug = NONE then
                      app safedelete (script :: intermediates)
                    else ()
          in
            isSuccess res
          end
        val script_part =
            if String.isSuffix "Script" script then
              String.substring(script, 0, size script - 6)
            else raise Fail "Invariant failure in run_script"
        val other_nodes = let
          open HM_DepGraph
        in
          diag (fn _ => "Looking for other nodes with buildscript "^script);
          find_nodes_by_command g
              (hmdir.curdir(),
               BuiltInCmd (BIC_BuildScript script_part, empty_incinfo))
              (* incinfos not consulted for comparison so empty value ok here *)
        end
      in
        BR_ClineK { cline = (useScript, cline), job_kont = cont,
                    other_nodes = other_nodes }
      end
  in
    let
    in
      case (c : (dep,GraphExtra.t) buildcmds) of
          Compile (deps,_) =>
          let
            val file = fromFile arg
            val _ = exists_readable file orelse
                    (warn ("Wanted to compile "^file^
                            ", but it wasn't there\n");
                     raise FileNotFound)
            val res = poly_compile warn diag true arg include_flags deps []
          in
            if OS.Process.isSuccess res then BR_OK else BR_Failed
          end
        | BuildScript (s, deps, extra : GraphExtra.t) =>
          let
            val (scriptetc,objectfiles) = setup_script s (deps,extra) []
          in
            run_script g extra scriptetc objectfiles
                       [s^"Theory.sml", s^"Theory.sig", s^"Theory.dat"]
          end
        | BuildArticle (s0, deps : dep list, extra) =>
          let
            open hm_target
            val s = s0 ^ ".art"
            val dep_set = Binaryset.addList(empty_tgtset, deps)
            val oldscript_str = s0 ^ "Script.sml"
            val fakescript_str = s ^ "Script.sml"(*
            val _ = Posix.FileSys.link {old = oldscript_str,
                                        new = fakescript_str }*)
            val loggingextras =
                case opentheory of SOME uo => [uo]
                                 | NONE => ["loggingHolKernel.uo"]
            val deps =
                (Binaryset.delete(dep_set, filestr_to_tgt oldscript_str)
                                 |> Binaryset.listItems) @
                [filestr_to_tgt fakescript_str]
            val ((script,inters),objectfiles) =
                setup_script s (deps,extra) loggingextras
          in
            run_script g extra (script,fakescript_str :: inters) objectfiles [s]
          end
        | ProcessArticle (s,extra) =>
          let
            val raw_art_file = ART (RawArticle s)
            val art_file = ART (ProcessedArticle s)
            val raw_art = fromFile raw_art_file
            val art = fromFile art_file
            val cline =
                ("/bin/sh",
                 ["/bin/sh", "-c",
                  "opentheory info --article -o " ^ art ^ " " ^ raw_art])
          in
            BR_ClineK {cline = cline, job_kont = (fn _ => OS.Process.isSuccess),
                       other_nodes = []}
          end
    end handle CompileFailed => BR_Failed
             | FileNotFound  => BR_Failed
  end
  fun mosml_build_command hm_env extra {noecho, ignore_error, command = c} deps=
    let
      open Holmake_types
      val isHolmosmlcc =
          String.isPrefix (perform_substitution hm_env [VREF "HOLMOSMLC-C"]) c
      val isHolmosmlc =
          String.isPrefix (perform_substitution hm_env [VREF "HOLMOSMLC"]) c
      val isMosmlc =
          String.isPrefix (perform_substitution hm_env [VREF "MOSMLC"]) c
      val {diag,...} = outs
      val diag = diag "mosml_build"
    in
      if isHolmosmlcc orelse isHolmosmlc orelse isMosmlc then let
        val _ = diag (fn _ => "Processing mosml build command: "^c)
      in
        case process_mosml_args outs (if isHolmosmlcc then " -c " ^ c else c) of
            (Mosml_compile (objs, src), I) =>
            SOME (poly_compile warn diag (noecho orelse quiet_flag)
                               (toFile src)
                               I
                               deps
                               objs)
          | (Mosml_link (result, objs), I) =>
            let
            in
              diag (fn _ => "Moscow ML command is link -o "^result^" ["^
                            String.concatWith ", " objs ^ "]");
              SOME (poly_link (noecho orelse quiet_flag) extra result
                              (map OS.Path.base objs))
            end
          | (Mosml_error, _) =>
            (warn ("*** Couldn't interpret Moscow ML command: "^c);
             SOME (OS.Process.failure))
      end
      else NONE
    end
  val jobs = #jobs (#core optv)
  open HM_DepGraph
  fun pr s = s
  fun interpret_graph (g,ok) =
      (if ok then OS.Process.success else OS.Process.failure, g)
  fun interpret_bres bres =
    case bres of
        BR_OK => true
      | BR_ClineK{cline = (_,cl), job_kont = k, ...} =>
          k warn (Systeml.systeml cl)
      | BR_Failed => false


  fun system s =
    Systeml.system_ps
      (if relocbuild then Systeml.build_after_reloc_envvar ^ "=1 " ^ s
       else s)

  val build_graph =
        (fn g =>
            graphbuildj1 {
              build_command = (fn g => fn ii => fn cmds => fn f =>
                                  build_command g ii cmds f |> interpret_bres),
              mosml_build_command = mosml_build_command,
              outs = outs,
              keep_going = keep_going,
              quiet = quiet_flag,
              hmenv = hmenv,
              system = system } g)
in
  {extra_impl_deps = [],
   build_graph = build_graph}
end

end (* struct *)
\<close>
external_file \<open>../HOL/tools/Holmake/Holmake.sml\<close>


(*FIXME ADD SHIMS to posix textIO
ML_file \<open>../HOL/tools/Holmake/poly/ProcessMultiplexor.sig\<close>
ML_file \<open>../HOL/tools/Holmake/poly/ProcessMultiplexor.sml\<close>

ML_file \<open>../HOL/tools/Holmake/poly/MB_Monitor.sig\<close>
ML_file \<open>../HOL/tools/Holmake/poly/MB_Monitor.sml\<close>
ML_file \<open>../HOL/tools/Holmake/poly/multibuild.sml\<close>
ML_file \<open>../HOL/tools/Holmake/poly/BuildCommand.sml\<close>*)
ML\<open>(*---------------------------------------------------------------------------
     A special purpose version of make that "does the right thing" in
     single directories for building HOL theories, and accompanying
     SML libraries.
 ---------------------------------------------------------------------------*)

structure Holmake =
struct

open Systeml Holmake_tools Holmake_types HOLFileSys
infix forces_update_of depforces_update_of |>

structure FileSys = HOLFileSys
structure Path = OS.Path
structure Process = OS.Process

fun slist_to_set slist =
    Binaryset.addList(Binaryset.empty String.compare, slist)
fun flist_to_set flist =
    Binaryset.addList(Binaryset.empty file_compare, flist)
fun slist_to_dset basedir slist =
    List.foldl
      (fn (s,dset) =>
          Binaryset.add(dset, hmdir.extendp {base=basedir, extension=s}))
      (Binaryset.empty hmdir.compare) slist
fun deplist_to_set ds = Binaryset.addList(hm_target.empty_tgtset, ds)
val filestr_to_tgt = hm_target.filestr_to_tgt
(* turn a variable name into a list *)
fun envlist env id = let
  open Holmake_types
in
  map dequote (tokenize (perform_substitution env [VREF id]))
end

fun chattiness_level (switches : HM_Core_Cline.t) =
  case (#debug switches, #verbose switches, #quiet switches) of
      (SOME _, _, _) => 3
    | (_, true, _) => 2
    | (_, _, true) => 0
    | _ => 1

fun main() = let

val execname = Path.file (CommandLine.name())
fun warn s = stdErr_out (execname^": "^s^"\n")
fun die s = (warn s; Process.exit Process.failure)
val original_dir = hmdir.curdir()

fun is_src_dir hmd =
    let val s = nice_dir (hmdir.pretty_dir hmd)
    in
      String.isPrefix "$(HOLDIR)/src/" s
    end
fun in_src () = is_src_dir (hmdir.curdir())
val originally_in_src = is_src_dir original_dir

(* Global parameters, which get set at configuration time *)
val HOLDIR0 = Systeml.HOLDIR;
val DEPDIR = ".HOLMK";
val LOGDIR = ".hollogs";

local
  val sigobj = OS.Path.concat(HOLDIR0, "sigobj")
  val frakS = String.implode (map Char.chr [0xF0,0x9D,0x94,0x96])
in
fun ppath s = if String.isPrefix sigobj s then
                frakS ^ String.extract(s,size sigobj,NONE)
              else s

fun pflist fs = concatWithf (ppath o fromFile) ", " fs
fun pdlist ds = concatWithf tgt_toString ", " ds
end


(** Command line parsing *)

(*** parse command line *)
fun apply_updates fs v = List.foldl (fn (f,v) => #update f (warn,v)) v fs

fun getcline args =
  let
    open GetOpt
    val (opts, rest) = getOpt {argOrder = Permute,
                               options = HM_Cline.option_descriptions,
                               errFn = die}
                              args
    fun is_varassign str =
      let
        val fs = String.fields (fn x => x = #"=") str
      in
        List.length fs = 2 andalso List.all (fn s => String.size s > 0) fs
      end
    val (vars, targets) = List.partition is_varassign rest
  in
    (opts, vars, targets)
  end

val (master_cline_options, cline_vars, targets) =
  getcline (CommandLine.arguments())

val master_cleanp = List.exists (fn s => member s targets)
                                ["clean", "cleanDeps", "cleanAll"]

val master_cline_nohmf =
    HM_Cline.default_options |> apply_updates master_cline_options

fun read_holpathdb() =
    let
      val holpathdb_extensions =
          holpathdb.search_for_extensions (fn s => [])
            {starter_dirs = [FileSys.getDir()], skip = holpathdb.db_dirs()}
      val _ = List.app holpathdb.extend_db holpathdb_extensions
      open Holmake_types
      fun foldthis {vname,path} env = env_extend (vname, [LIT path]) env
    in
      holpathdb.fold foldthis (HM_BaseEnv.make_base_env master_cline_nohmf)
    end

val master_cline_option_value = #core master_cline_nohmf
val usepfx = #jobs master_cline_option_value = 1
val {warn=warn0,info=info0,diag=diag0,...} =
      output_functions {chattiness = chattiness_level master_cline_option_value,
                        debug = #debug master_cline_option_value,
                        usepfx = usepfx}

val _ = diag0 "startup"
          (fn _ => "Started and have initial diagnostic/messaging functions")

(* execute pre-execs *)
val _ =
    if master_cleanp orelse #help master_cline_option_value then ()
    else
      let
        val preexec_map =
            holpathdb.files_upward_in_hierarchy
              ReadHMF.find_includes
              {diag = diag0 "read-preexecs"}
              {filename = ".hol_preexec",
               starter_dirs = [FileSys.getDir()],
               skip = empty_strset}

        val _ = diag0 "startup"
                      (fn _ => "Read preexec_map, with " ^
                               Int.toString (Binarymap.numItems preexec_map) ^
                               " entries")
        val (msg,pfx) =
            if #no_preexecs master_cline_option_value then
              (info0, "Not executing")
            else (warn0, "Executing")
        val esc = String.translate (fn #"'" => "'\\''" | c => str c)
        fun appthis (k,c0) =
            let
              open Substring
              val c =
                  (if Systeml.OS = "winNT" then ""
                   else "HOLORIG="^esc (hmdir.toAbsPath original_dir) ^ " ") ^
                  string (dropr Char.isSpace (full c0))
              val _ =
                  msg (pfx ^ " " ^ OS.Path.concat(k,".hol_preexec") ^
                       ":\n  " ^ c)
      in
        if #no_preexecs master_cline_option_value then ()
        else
          let val _ = FileSys.chDir k
              val res = OS.Process.system c
          in
            if OS.Process.isSuccess res then hmdir.chdir original_dir
            else die "** FAILED"
          end
            end
      in
        Binarymap.app appthis preexec_map
      end

(* The hmftext is the form of the target as it appears in the Holmakefile *)
type tgt_ruledb = (dep, {hmftext: string, dependencies:dep list,
                         commands : quotation list})
                    Binarymap.dict
val empty_trdb : tgt_ruledb = Binarymap.mkDict hm_target.compare

(* Extend the base environment with vars passed at commandline (foldl below),
   as well as environment variables "magically" derived from other options,
   (handled by HM_Core_Cline.extend_env). *)
fun extend_with_cline_vars env =
    let val env =
            List.foldl (fn (vstr, env) =>
                           case String.fields (fn x => x = #"=") vstr of
                               [vname, contents] =>
                                 env_extend (vname, [LIT contents]) env
                             | _ => die ("Malformed variable assignment " ^
                                         "passed at commandline: " ^ vstr))
                       env
                       cline_vars
    in
      HM_Core_Cline.extend_env (#core master_cline_nohmf) env
    end


local
  open hm_target
  val base = extend_with_cline_vars (read_holpathdb())

  val hmcache = ref (Binarymap.mkDict String.compare)
  val default = (base,empty_trdb,NONE)
  fun get_hmf0 d =
      if FileSys.access("Holmakefile", [FileSys.A_READ]) then
        let
          val (env, rdb, tgt0) =
              ReadHMF.diagread {warn=warn0,die=die,info=info0}
                               "Holmakefile"
                               (extend_with_cline_vars (read_holpathdb()))
              handle Fail s =>
                     (die ("Bad Holmakefile in " ^ d ^ ": " ^ s);
                      (base,Binarymap.mkDict String.compare,NONE))
          fun hmfstr_to_tgt s = s |> filestr_to_tgt |> setHMF_text s
          fun foldthis (k,{commands,dependencies=deps0},A) =
              Binarymap.insert(A, filestr_to_tgt k,
                               {commands = commands, hmftext = k,
                                dependencies = map hmfstr_to_tgt deps0})
        in
          (env, Binarymap.foldl foldthis empty_trdb rdb,
           Option.map filestr_to_tgt tgt0)
        end
      else
        default
in
fun get_hmf () =
    let
      val d = FileSys.getDir()
    in
      case Binarymap.peek(!hmcache, d) of
          NONE => let val result = get_hmf0 d
                  in
                    hmcache := Binarymap.insert (!hmcache, d, result);
                    result
                  end
        | SOME r => r
    end
end

fun getnewincs dir =
    let val (env, _, _) = get_hmf()
    in
      {includes = envlist env "INCLUDES" |> slist_to_dset dir,
       preincludes = envlist env "PRE_INCLUDES" |> slist_to_dset dir}
    end

(* Examining the c/line options, determine whether to use a
   Holmakefile at all, and which one if we are going to use one.
*)
val (cline_hmakefile, cline_nohmf) =
    List.foldl (fn (f,(hmf,nohmf)) =>
                   ((case #hmakefile f of NONE => hmf | SOME s => SOME s),
                    nohmf orelse #no_hmf f))
               (NONE,false)
               master_cline_options

fun get_hmf_cline_updates hmenv =
  let
    val hmf_cline = envlist hmenv "CLINE_OPTIONS"
    val (hmf_options, _, hmf_rest) = getcline hmf_cline
    val _ = if null hmf_rest then ()
            else
              warn ("Unused c/line options in makefile: "^
                    String.concatWith " " hmf_rest)
  in
    hmf_options
  end


val starting_holmakefile =
    if cline_nohmf then NONE
    else
      case cline_hmakefile of
          NONE => if exists_readable "Holmakefile" then SOME "Holmakefile"
                  else NONE
        | x => x

val (start_hmenv, start_rules, start_tgt) = get_hmf()

val start_envlist = envlist start_hmenv
val start_options = start_envlist "OPTIONS"

val option_value : HM_Cline.t =
    HM_Cline.default_options
      |> apply_updates (get_hmf_cline_updates start_hmenv)
      |> apply_updates master_cline_options
val coption_value = #core option_value
val cmdl_HOLDIR = #holdir coption_value
val HOLDIR    = case cmdl_HOLDIR of NONE => HOLDIR0 | SOME s => s
val SIGOBJ    = normPath(Path.concat(HOLDIR, "sigobj"));


(* things that need to be read out of the first Holmakefile, and which will
   govern the behaviour even when recursing into other directories that may
   have their own Holmakefiles *)
val (outputfns as {warn,tgtfatal,diag,info,chatty,info_inline,info_inline_end})=
    output_functions {chattiness = chattiness_level coption_value,
                      debug = #debug coption_value,
                      usepfx = usepfx}
val do_logging_flag = #do_logging coption_value
val no_lastmakercheck = #no_lastmaker_check coption_value
val show_usage = #help coption_value
val quit_on_failure = #quit_on_failure coption_value
val toplevel_no_prereqs = #no_prereqs coption_value
val toplevel_no_overlay = #no_overlay coption_value
val cline_additional_includes = #includes coption_value
val cline_always_rebuild_deps = #rebuild_deps coption_value
val cline_nobuild = #no_action coption_value
val cline_recursive_build = #recursive_build coption_value
val cline_recursive_clean = #recursive_clean coption_value

(* make the cline includes = [] so that these are only looked at once
   (when the cline_additional_includes value is folded into dirinfo values
   and eventually used in hm_recur).
*)
val pass_option_value =
    HM_Cline.fupd_core (HM_Core_Cline.fupd_includes (fn _ => [])) option_value

val _ = do_lastmade_checks outputfns {no_lastmakercheck = no_lastmakercheck}

val _ = diag "startup" (fn _ => "CommandLine.name() = "^CommandLine.name())
val _ = diag "startup"
             (fn _ => "CommandLine.arguments() = "^
                      String.concatWith ", " (CommandLine.arguments()))

(* set up logging *)
val logfilename = Systeml.make_log_file
val hostname = if Systeml.isUnix then
                 case Mosml.run "hostname" [] "" of
                   Mosml.Success s => String.substring(s,0,size s - 1) ^ "-"
                                      (* substring to drop \n in output *)
                 | _ => ""
               else "" (* what to do under windows? *)

fun finish_logging buildok = let
in
  if do_logging_flag andalso FileSys.access(logfilename, []) then let
      open Date
      val timestamp = fmt "%Y-%m-%dT%H%M" (fromTimeLocal (Time.now()))
      val newname0 = hostname^timestamp
      val newname = (if buildok then "" else "bad-") ^ newname0
    in
      FileSys.rename {old = logfilename, new = newname};
      buildok
    end
  else buildok
end handle IO.Io _ => (warn "Had problems making permanent record of make log";
                       buildok)

val _ = Process.atExit (fn () => ignore (finish_logging false))

(* ----------------------------------------------------------------------

    recursively

    The hm parameter is how work is actually done; this parameter is
    called when all of the necessary recursion has been performed and
    work should be done in the current ("local") directory. (We are
    performing a post-order depth-first traversal.)

    Finally, what of the dirinfo?

    This record includes
        includes: the includes that the local directory knows about
                  (which will have come from the command-line or
                  INCLUDES lines in the local Holmakefile
     preincludes: similarly
         visited: a set of visited directories (with directories
                  expressed as absolute paths)

    The includes and preincludes are clearly useful when it comes time to
    do any local work, but also specify how the recursion is to happen.

    Now, the recursion into those directories may result in extra
    includes and preincludes.
   ---------------------------------------------------------------------- *)
fun idm_lookup idm key =
  case Binarymap.peek(idm, key) of
      NONE => {pres = empty_dirset, incs = empty_dirset}
    | SOME r => r

fun extend_idmap k (v as {incs = i,pres = p}) idm0 =
  case Binarymap.peek(idm0, k) of
      NONE => Binarymap.insert(idm0, k, v)
    | SOME {incs = i0, pres = p0} =>
        Binarymap.insert(idm0, k,
                         {incs = Binaryset.union(i0,i),
                          pres = Binaryset.union(p0,p)})

fun print_set ds =
  "{" ^ set_concatWith hmdir.pretty_dir ", " ds ^ "}"

type incmap = (hmdir.t, {incs:dirset,pres:dirset}) Binarymap.dict
type dirinfo = {incdirmap : incmap, visited : hmdir.t Binaryset.set,
                ancestors : hmdir.t list (* most recent hd of list *)}
type 'a hmfold =
     {includes : string list, preincludes : string list} ->
     (string -> unit) ->
     hmdir.t ->
     'a -> 'a

fun find_upto cmp pfx x els =
    case els of
        [] => NONE
      | h::t => if cmp (h,x) = EQUAL then SOME (h::pfx)
                else find_upto cmp (h::pfx) x t
(* ----------------------------------------------------------------------

    Parameters
           getnewincs : get INCLUDES information from a directory,
                        type : dir -> dirinfo

           {warn : how to issue a warning,
            diag : how to issue a diagnostic,
            hm   : what to do in a given directory;
                   will be either to build a graph, or to perform a clean
            dirinfo : tracks INCLUDES info, and the progress of the
                      recursion
            dir : the directory I'm in,
            data : the value to fold hm over, a graph for a normal build,
                   or just unit for a clean}

    Assume that we are already in directory dir, and will end in the same
    directory.

   ---------------------------------------------------------------------- *)
fun 'a recursively getnewincs dsopt {outputfns,verb,hm,dirinfo,dir,data} =
let
  val {incdirmap,visited,ancestors} = dirinfo : dirinfo
  val hm : 'a hmfold = hm
  val {warn,diag,info,chatty,...} : output_functions = outputfns
  val {includes=incset, preincludes = preincset} = getnewincs dir
  val incdirmap =
      incdirmap |> extend_idmap dir {incs = incset, pres = preincset}
                |> (case dsopt of
                        SOME ds => extend_idmap dir {incs=ds,pres=empty_dirset}
                      | NONE => (fn x => x))
  val recur_into = set_union (set_union incset preincset)
                             (case dsopt of NONE => empty_dirset
                                          | SOME ds => ds)
  fun recur_abbrev dir data (dirinfo:dirinfo) =
      recursively getnewincs NONE
                  {outputfns = outputfns,verb=verb,hm=hm,dirinfo=dirinfo,
                   dir=dir, data=data}
  val diag = diag "builddepgraph"
  val _ = diag (fn _ => "recursively: call in " ^ hmdir.pretty_dir dir)
  val _ = diag (fn _ => "recursively: includes (pre- & normal) = [" ^
                        set_concatWith hmdir.pretty_dir ", " recur_into ^ "]")
  val _ = diag (fn _ =>
                   "recursively: incdmap on dir " ^ hmdir.pretty_dir dir ^
                   " = " ^ print_set (#incs (idm_lookup incdirmap dir)))
  val _ = diag (fn _ =>
                   "recursively: ancestor chain = " ^
                   String.concatWith ", " (map hmdir.pretty_dir ancestors))
  fun recurse (acc as {visited,incdirmap,data:'a}) newdir = let
    val _ =
        case find_upto hmdir.compare [newdir] newdir ancestors of
            NONE => ()
          | SOME badchain =>
            let
              val diag = if verb = "Cleaning" then warn
                         else (fn s => (#tgtfatal outputfns s;
                                        OS.Process.exit OS.Process.failure))
            in
              diag ("INCLUDES chain loops:\n  " ^
                    String.concatWith " -->\n  "
                                      (map hmdir.pretty_dir badchain))
            end
  in
    if Binaryset.member(visited, newdir) then
      (* even if you don't want to rebuild newdir, you still want to learn
         about what it depends on so that the dependency map for this directory
         is appropriately augmented *)
      {visited = visited,
       data = data,
       incdirmap = extend_idmap dir (idm_lookup incdirmap newdir) incdirmap}
    else let
      val _ = FileSys.access
                (hmdir.toAbsPath newdir, [FileSys.A_READ, FileSys.A_EXEC])
              orelse
                die ("Attempt to recurse into non-existent directory: " ^
                     hmdir.pretty_dir newdir ^
                     "\n  (Probably a result of bad INCLUDES spec.)")
      val _ = diag (fn _ => "recursively: Visited set = " ^ print_set visited)
      val _ = FileSys.chDir (hmdir.toAbsPath newdir)
      val result =
          case recur_abbrev newdir data
                            {incdirmap=incdirmap, visited=visited,
                             ancestors = newdir :: ancestors}
           of
              {visited,incdirmap = idm0,data=data'} =>
              {visited = visited,
               incdirmap = extend_idmap dir (idm_lookup idm0 newdir) idm0,
               data = data'}
      val _ = FileSys.chDir (hmdir.toAbsPath dir)
    in
      case result of
          {visited,incdirmap,data} =>
          let
            val {incs,pres} = idm_lookup incdirmap dir
          in
            diag (fn () =>
                     "recursively: computed includes for " ^
                     hmdir.pretty_dir dir ^ " = " ^ print_set incs);
            diag (fn () =>
                     "recursively: computed pre-includes for " ^
                     hmdir.pretty_dir dir ^ " = " ^ print_set pres)
          end;
      result
    end
  end
  fun do_em (accg as {incdirmap,data:'a,visited}) dirs =
      case dirs of
          [] =>
          let
            val {pres, incs} = idm_lookup incdirmap dir
            val f = Binaryset.foldr (fn (d,acc) => hmdir.toAbsPath d :: acc) []
            val _ = if not (isSome dsopt) then
                      info_inline (verb ^ " " ^ bold (hmdir.pretty_dir dir))
                    else ()
            val data' = hm {includes=f incs,preincludes=f pres} warn dir data
          in
            {incdirmap = incdirmap, visited = visited, data = data'}
          end
        | x::xs => do_em (recurse accg x) xs
  val visited = Binaryset.add(visited, dir)
  val result =
      do_em {visited = visited, incdirmap = incdirmap, data = data}
            (Binaryset.listItems recur_into)
in
  diag (fn _ => "recursively: Finished work in "^hmdir.pretty_dir dir);
  result
end

(* prepare to do logging *)
val () = if do_logging_flag then
           if FileSys.access (logfilename, []) then
             warn "Make log exists; new logging will concatenate on this file"
           else let
               (* touch the file *)
               val outs = openOut logfilename
             in
               closeOut outs
             end handle IO.Io _ => warn "Couldn't set up make log"
         else ()

val actual_overlay =
    if toplevel_no_overlay orelse member "NO_OVERLAY" start_options then NONE
    else SOME DEFAULT_OVERLAY

val std_include_flags = [SIGOBJ]

fun get_rule_info rdb env tgt =
    case Binarymap.peek(rdb, tgt) of
      NONE => NONE
    | SOME {dependencies, commands, hmftext} =>
      let
        fun special tgt' =
            valOf (hm_target.HMF_text tgt')
            handle Option =>
                   die ("No Holmakefile text for " ^ tgt_toString tgt' ^
                        " in rule for " ^ tgt_toString tgt)
        val dep1 = [LIT (special (hd dependencies))] handle Empty => [LIT ""]
        val env = env |> env_extend("<", dep1)
                      |> env_extend("@", [LIT hmftext])
      in
        SOME {dependencies = dependencies,
              commands = map (perform_substitution env) commands}
      end

fun local_rule_info t =
    let val (env, rules, _) = get_hmf()
    in
      get_rule_info rules env t
    end

fun extra_deps t =
      Option.map #dependencies (local_rule_info t)
fun localstr_extra_deps s =
    extra_deps (hm_target.mk(hmdir.curdir(), toFile s))

fun isPHONY t =
    case localstr_extra_deps ".PHONY" of
        NONE => false
      | SOME l => List.exists (fn e => hm_target.compare(e,t) = EQUAL) l

fun extra_commands t = Option.map #commands (local_rule_info t)

fun extra_targets() =
    let
      val (_, rules, _) = get_hmf()
    in
      Binarymap.foldr (fn (k,_,acc) => k::acc) [] rules
    end

fun extra_rule_for t = local_rule_info t
fun dir_varying_envlist s =
    let val (env, _, _) = get_hmf()
    in
      envlist env s
    end

fun extra_cleans() = dir_varying_envlist "EXTRA_CLEANS"

(*** Compilation of files *)
val binfo : HM_Cline.t BuildCommand.buildinfo_t =
    {optv = option_value,
     actual_overlay = actual_overlay, envlist = dir_varying_envlist,
     hmenv = start_hmenv,
     quit_on_failure = quit_on_failure, outs = outputfns,
     SIGOBJ = SIGOBJ}
val {extra_impl_deps,build_graph} = BuildCommand.make_build_command binfo

val _ = let
in
  diag "startup" (fn _ => "HOLDIR = "^HOLDIR);
  diag "startup" (fn _ => "Targets = [" ^ String.concatWith ", " targets ^ "]");
  diag "startup" (fn _ => "Additional includes = [" ^
                          String.concatWith ", "
                                            cline_additional_includes ^ "]");
  diag "startup" (fn _ => "Additional Holmake variables = [" ^
                          String.concatWith "," cline_vars ^ "]");
  diag "startup" (fn _ => HM_BaseEnv.debug_info option_value)
end

(** Top level sketch of algorithm *)
(*

   We have the following relationship --> where this arrow should be read
   "leads to the production of in one step"

    *.sml --> *.uo                          [ mosmlc -c ]
    *.sig --> *.ui                          [ mosmlc -c ]
    *Script.uo --> *Theory.sig *Theory.sml
       [ running the *Script that can be produced from the .uo file ]
    *Script.uo --> *.art
       [ running the *Script with proof-recording enabled ]
    *.art --> *.ot.art
       [ opentheory info --article ]

   (where I have included the tool that achieves the production of the
   result in []s)

   However, not all productions can go ahead with just the one principal
   dependency present.  Sometimes other files are required to be present
   too.  We don't know which other files which are required, but we can
   find out by using Ken's holdep tool.  (This works as follows: given the
   name of the principal dependency for a production, it gives us the
   name of the other dependencies that exist in the current directory.)

   In theory, we could just run holdep everytime we were invoked, and
   with a bit of luck we'll design things so it does look as if really
   are computing the dependencies every time.  However, this is
   unnecessary work as we can cache this information in files and just
   read it in from these.  Of course, this introduces a sub-problem of
   knowing that the information in the cache files is up-to-date, so
   we will need to compare time-stamps in order to be sure that the
   cached dependency information is up to date.

   Another problem is that we might need to build a dependency DAG but
   in a situation where elements of the principal dependency chain
   were themselves out of date.
*)

(* The primary dependency chain does not depend on anything in the
   file-system; it always looks the same.  However, additional
   dependencies depend on what holdep tells us.  This function that
   runs holdep, and puts the output into specified file, which will live
   in DEPDIR somewhere. *)

fun get_implicit_dependencies incinfo (f: File) : dep Binaryset.set = let
  val {preincludes,includes} = incinfo
  val file_dependencies0 =
      get_direct_dependencies {incinfo = incinfo,
                               extra_targets = extra_targets(),
                               output_functions = outputfns,
                               DEPDIR = DEPDIR} f
  val diag = diag "impdeps"
  val _ = diag (fn _ => "get_implicit_dependencies("^fromFile f^"), " ^
                        "directdeps = " ^ pdlist file_dependencies0)
  val file_dependencies =
      case actual_overlay of
        NONE => file_dependencies0
      | SOME s => if isSome (holdep_arg f) then
                    filestr_to_tgt (fullPath [SIGOBJ, s]) :: file_dependencies0
                  else
                    file_dependencies0
  fun requires_exec (SML (Theory _)) = true
    | requires_exec (SIG (Theory _)) = true
    | requires_exec (ART (RawArticle _)) = true
    | requires_exec (DAT _) = true
    | requires_exec _                = false
in
  if requires_exec f then let
      (* because we have to build an executable in order to build a
         theory, this build depends on all of the dependencies
         (meaning the transitive closure of the direct dependency
         relation) in their .UO form, not just .UI *)
      val get_direct_dependencies =
          get_direct_dependencies {incinfo = incinfo, DEPDIR = DEPDIR,
                                   output_functions = outputfns,
                                   extra_targets = extra_targets()}
      val starters = get_direct_dependencies f
      (* ignore theories as we don't want to depend on the script files
         behind them *)
      fun collect_all_dependencies sofar tovisit =
          case tovisit of
            [] => sofar
           | d::ds =>
             case hm_target.filepart d of
                 UO (Theory _) => collect_all_dependencies sofar ds
               | UI (Theory _) => collect_all_dependencies sofar ds
               | _ =>
                 let
                   open hm_target
                   val deps =
                       if hmdir.compare(dirpart d, hmdir.curdir()) <> EQUAL
                       then []
                       else
                         case filepart d of
                             UI x => (get_direct_dependencies f @
                                      get_direct_dependencies (UO x))
                           | _ => get_direct_dependencies f
                   val newdeps = set_diff (deplist_to_set deps) sofar
                 in
                   collect_all_dependencies (set_union sofar newdeps)
                                            (listItems newdeps @ ds)
                 end
      val tcdeps = collect_all_dependencies (deplist_to_set starters) starters
      val _ = diag (fn _ => "get_implicit_dependencies("^fromFile f^"), " ^
                            "tcdeps = " ^
                            set_concatWith tgt_toString ", " tcdeps)
      val uo_deps =
          Binaryset.foldl
            (fn (d, A) => case hm_target.filepart d of
                              UI x => set_add (hm_target.setFile (UO x) d) A
                            | _ => A)
            hm_target.empty_tgtset
            tcdeps
      val alldeps = set_addList (file_dependencies @ extra_impl_deps)
                                (set_union tcdeps uo_deps)
    in
      case f of
        SML x => let
          (* there may be theory files mentioned in the Theory.sml file that
             aren't mentioned in the script file.  If so, we are really
             dependent on these, and should add them.  They will be listed
             in the dependencies for UO (Theory x). *)
          val additional_theories =
              if exists_readable (fromFile f) then
                set_mapPartial
                  (fn dep => case hm_target.filepart dep of
                                 UO (Theory s) => SOME dep
                               | _ => NONE)
                  hm_target.empty_tgtset
                  (get_implicit_dependencies incinfo (UO x))
              else hm_target.empty_tgtset
        in
          set_union alldeps additional_theories
        end
      | _ => alldeps
    end
  else
    deplist_to_set file_dependencies
end

fun get_explicit_dependencies (f:File) : dep list =
    let
      val result = case extra_deps (filestr_to_tgt (fromFile f)) of
                       SOME deps => deps
                     | NONE => []
    in
      diag "expdeps" (fn _ => fromFile f ^ " -explicitdeps-> " ^ pdlist result);
      result
    end

val slist_to_depset =
    List.foldl (fn (s,set) => Binaryset.add(set, filestr_to_tgt s))
               hm_target.empty_tgtset
fun dset_union ds1 ds2 =
    Binaryset.listItems
      (Binaryset.union(deplist_to_set ds1, deplist_to_set ds2))



(** Build graph *)

exception CircularDependency
exception BuildFailure
exception NotFound

fun no_full_extra_rule tgtopt =
    case tgtopt of
        NONE => true
      | SOME tgt => case extra_commands tgt of NONE => true | SOME cl => null cl

val done_some_work = ref false
open HM_DepGraph

fun is_script s =
  case toFile s of
      SML (Script _) => true
    | _ => false

fun de_script s =
  case toFile s of
      SML (Script s) => SOME s
    | _ => NONE

type cdelem = hmdir.t * string
type cdset = cdelem Binaryset.set * cdelem list
val empty_cdset =
    (Binaryset.empty (pair_compare(hmdir.compare, String.compare)), [])
fun cdset_add (set,stk) e = (Binaryset.add(set,e), e::stk)
fun cdset_member(set,stk) e = Binaryset.member(set,e)
fun cdset_toString ((_,stk):cdset) =
    String.concatWith ">" (map #2 (List.rev stk))

(* is run in a directory at a time *)
type g = GraphExtra.t HM_DepGraph.t
fun build_depgraph cdset incinfo (tgt:dep) g0:(g * node) =
let
  val dir = hm_target.dirpart tgt and target = hm_target.filepart tgt
  val {preincludes,includes} = incinfo
  val incinfo = {preincludes = preincludes,
                 includes = includes @ std_include_flags}
  val pdep = primary_dependent target
  val target_s = tgt_toString tgt
  val actual_dir = hmdir.curdir()
  fun fp d s = hmdir.extendp {base = d, extension = s}
  fun fps d = hmdir.toAbsPath d
  fun addF tgt n = (n,tgt)
  fun nstatus g n = peeknode g n |> valOf |> #status
  fun build (tgt':dep) g =
    build_depgraph (cdset_add cdset (dir, target_s)) incinfo tgt' g

  val fullpath = fp dir target_s
  val fullpath_s = fps fullpath
  val pretty_tgt = hmdir.pretty_dir fullpath
  val (env, _, _) = get_hmf()
  val extra = GraphExtra.get_extra { master_dir = original_dir,
                                     master_cline = option_value,
                                     envlist = envlist env }
  val extra_deps = if GraphExtra.canIgnore tgt extra then []
                   else GraphExtra.extra_deps extra
  val diag = fn f => diag "builddepgraph"
                          (fn _ => "|" ^ cdset_toString cdset ^ "| " ^ f ())
  val _ = diag (fn _ => "Target = " ^ pretty_tgt)
  val _ = diag (fn _ => "Extra = " ^ GraphExtra.toString extra)
  val _ = not (cdset_member cdset (dir,target_s)) orelse
          die (pretty_tgt ^ " seems to depend on itself failing\n" ^
               " Loop is : " ^ cdset_toString cdset ^ ">" ^ pretty_tgt)
in
  case target_node g0 tgt of
      (x as SOME n) => (g0, n)
    | NONE =>
      if not (hmdir.eqdir dir actual_dir) andalso
         no_full_extra_rule (SOME tgt)
         (* path outside of current directory *)
      then (
        diag (fn _ => "Target "^pretty_tgt^" external to directory");
        add_node {target = tgt, seqnum = 0, phony = false,
                  status = if exists_readable fullpath_s then Succeeded
                           else Failed{needed=false},
                  dir = dir, extra = extra,
                  command = NoCmd, dependencies = []} g0
      )
      else if isSome pdep andalso no_full_extra_rule (SOME tgt) then
        let
          val pdep = hm_target.mk(dir, valOf pdep)
          val (g1, pnode) = build pdep g0
          val _ = diag (fn _ => "Extended graph with primary dependency for " ^
                                target_s)
          val secondaries =
              set_addList (get_explicit_dependencies target)
                          (get_implicit_dependencies incinfo target)
                       |> set_addList extra_deps
          val _ = diag (fn _ => target_s ^ " -secondaries-> " ^
                                set_concatWith tgt_toString ", " secondaries)
          fun foldthis (d, (g, secnodes)) =
            let
              val (g', n) = build d g
            in
              (g', addF d n::secnodes)
            end
          val (g2, depnodes : (HM_DepGraph.node * dep) list) =
              Binaryset.foldl foldthis (g1, [addF pdep pnode]) secondaries
          val unbuilt_deps =
              List.filter (fn (n,_) => let val stat = nstatus g2 n
                                       in
                                         is_pending stat orelse is_failed stat
                                       end)
                          depnodes
          val needs_building =
              not (null unbuilt_deps) orelse
              set_exists (fn d => d depforces_update_of tgt)
                         (set_add pdep secondaries)
          val bic = case toFile target_s of
                        SML (Theory s) => BIC_BuildScript s
                      | SIG (Theory s) => BIC_BuildScript s
                      | DAT s => BIC_BuildScript s
                      | _ => BIC_Compile
        in
            add_node {target = tgt, seqnum = 0, phony = false,
                      status = if needs_building then Pending{needed=false}
                               else Succeeded,
                      extra = extra,
                      command = BuiltInCmd (bic,incinfo), dir = hmdir.curdir(),
                      dependencies = depnodes } g2
        end
      else
        case extra_rule_for tgt of
            NONE => (
              diag (fn _ => "No extra info/rule for target " ^ target_s);
              add_node {target = tgt, seqnum = 0, phony = false,
                        status = if exists_readable target_s then Succeeded
                                 else Failed{needed=false},
                        command = NoCmd, dir = hmdir.curdir(), extra = extra,
                        dependencies = []} g0
            )
          | SOME {dependencies, commands, ...} =>
            let
              val _ = diag (fn _ => target_s ^ " has rule")
              fun foldthis (d, (g, secnodes)) =
                let
                  val (g, n) = build d g
                in
                  (g, addF d n::secnodes)
                end
              fun depfoldthis (dep, (starp, deps)) =
                  let
                    open hm_target
                    val d = dirpart dep and f = filepart dep
                  in
                    case f of
                        SML (Script s) =>
                        if String.sub(s,0) = #"*" then
                          if isSome starp then
                            die
                              ("Multiple starred script dependencies for "^
                               target_s)
                          else if hmdir.compare(d, actual_dir) <> EQUAL then
                            die "Don't star non-local script files"
                          else
                            let
                              val s' = String.extract(s,1,NONE)
                            in
                              (SOME s',
                               (mk(d, SML (Script s')) |> setHMF_text s') ::
                               deps)
                            end
                        else (starp, dep :: deps)
                      | _ => (starp, dep :: deps)
                  end
              val (starred_dep, dependencies) =
                  if null commands then
                    List.foldr depfoldthis (NONE, []) dependencies
                  else (NONE, dependencies)
              val _ = case starred_dep of
                          SOME s =>
                            diag (fn _ => target_s ^ " has star = " ^ s)
                        | NONE => diag (fn _ => "No star for " ^ target_s)

              val more_deps =
                  case starred_dep of
                      NONE => hm_target.empty_tgtset
                    | SOME s =>
                        get_implicit_dependencies
                          incinfo
                          (SML(Theory s))
                          handle Option => die "more_deps invariant failure"
                               | e => die (
                                       "Unexpected exception: " ^
                                       General.exnMessage e ^
                                       " thrown in get_implicit_dependencies"
                                     )

              val (g1, depnodes) =
                  Binaryset.foldl foldthis (g0, [])
                                  (more_deps |> set_addList dependencies
                                             |> set_addList extra_deps)

              val unbuilt_deps =
                  List.filter
                    (fn (n,_) => let val stat = nstatus g1 n
                                 in
                                   is_pending stat orelse is_failed stat
                                 end)
                    depnodes
              val is_phony = isPHONY tgt
              val _ = if is_phony then diag (fn _ => target_s ^" is phony")
                      else ()
              val needs_building_by_deps_existence =
                  not (FileSys.access(target_s, [])) orelse
                  not (null unbuilt_deps) orelse
                  List.exists (fn d => d depforces_update_of tgt)
                              dependencies orelse
                  is_phony
              val needs_building =
                  needs_building_by_deps_existence andalso
                  not (null commands)
              val _ = if is_phony then
                        diag (fn _ => target_s ^ " needs building = " ^
                                      Bool.toString needs_building)
                      else ()
              val status = if needs_building then Pending{needed=false}
                           else Succeeded
              fun foldthis (c, (depnode, seqnum, g)) =
                let
                  val (g',n) = add_node {target = tgt, seqnum = seqnum,
                                         status = status, phony = is_phony,
                                         command = SomeCmd c, extra = extra,
                                         dir = hmdir.curdir(),
                                         dependencies = depnode @ depnodes } g
                in
                  (* This function needs to be folded l-to-r to ensure that
                     the last node is the one that gets recorded in the target
                     map, ensuring that if targets are marked as needed, the
                     earliest commands will get executed as dependencies of
                     the later commands *)
                  ([(n,tgt)], seqnum + 1, g')
                end
            in
              if needs_building then
                let
                  val (lastnodelist, _, g) =
                      List.foldl foldthis ([], 0, g1) commands
                in
                  (g, #1 (hd lastnodelist))
                end
              else
                case starred_dep of
                    NONE =>
                    add_node {target = tgt, seqnum = 0, phony = is_phony,
                              status = status, command = NoCmd, extra = extra,
                              dir = hmdir.curdir(), dependencies = depnodes} g1
                  | SOME s =>
                    let
                      val updstatus =
                          if needs_building_by_deps_existence then
                            Pending{needed=false}
                          else Succeeded
                      val fp = OS.Path.concat (hmdir.toAbsPath actual_dir, s)
                    in
                      add_node {target = tgt, seqnum = 0,
                                phony = false, status = updstatus,
                                command = BuiltInCmd
                                            (BIC_BuildScript fp, incinfo),
                                dir = dir, extra = extra,
                                dependencies = depnodes} g1
                    end
            end
end

(* called in dir *)
fun get_targets dir =
    let
      val from_directory =
          deplist_to_set (generate_all_plausible_targets warn NONE)
      val (_, rules, _) = get_hmf()
    in
      Binarymap.foldl (fn (dep,v,acc) =>
                          if hm_target.filepart dep <> Unhandled ".PHONY" then
                            set_add dep acc
                          else acc)
                      from_directory
                      rules
    end

fun extend_graph_in_dir incinfo warn dir graph =
    let
      open HM_DepGraph
      val _ = diag "builddepgraph" (fn _ =>
                       "Extending graph in directory " ^ hmdir.pretty_dir dir)
      val dir_targets = get_targets dir
    in
      Binaryset.foldl
        (fn (t,g) => #1 (build_depgraph empty_cdset incinfo t g))
        graph
        dir_targets
    end

fun create_complete_graph cline_incs idm =
    let
      val d = hmdir.curdir()
      val {data = g, incdirmap, visited, ...} =
          recursively getnewincs (SOME cline_incs) {
            outputfns = outputfns, verb = "Scanning",
            hm=extend_graph_in_dir,
            dirinfo={incdirmap=idm, visited = Binaryset.empty hmdir.compare,
                     ancestors = [original_dir]},
            dir = d,
            data = HM_DepGraph.empty()
          }
      val numScanned = Binaryset.numItems visited
      val _ = if numScanned > 1 then
                (#info_inline outputfns ("Scanned " ^ Int.toString numScanned ^
                                         " directories");
                 #info_inline_end outputfns())
              else ()
      val diag = diag "builddepgraph"
    in
      diag (fn _ => "Finished building complete dep graph (has " ^
                    Int.toString (HM_DepGraph.size g) ^ " nodes)");
      (g,idm_lookup incdirmap d)
    end

fun clean_deps() =
  ( Holmake_tools.clean_depdir {depdirname = DEPDIR}
  ; Holmake_tools.clean_depdir {depdirname = LOGDIR} )

fun do_clean_target x = let
  fun clean_action () =
      Holmake_tools.clean_dir outputfns {extra_cleans = extra_cleans()}
in
  if originally_in_src orelse not (in_src()) then
    case x of
        "clean" => clean_action()
      | "cleanDeps" => ignore (clean_deps())
      | "cleanAll" => (clean_action(); ignore (clean_deps()))
    | _ => die ("Bad clean target " ^ x)
  else ()
end

val _ = not cline_always_rebuild_deps orelse clean_deps()

val cline_incs = slist_to_dset original_dir cline_additional_includes
val idmap0 = extend_idmap original_dir
                    {pres = empty_dirset, incs = empty_dirset}
                    empty_incdirmap

fun toplevel_build_graph () = create_complete_graph cline_incs idmap0

fun get_targets_recursively {incs, pres} =
    let
      val dirs = set_add original_dir (set_union incs pres)
      fun indir() =
          let val (_, _, target1) = get_hmf()
          in
            generate_all_plausible_targets warn target1
          end
    in
      List.concat (
        Binaryset.foldl
          (fn (d,A) => pushdir (hmdir.toAbsPath d) indir () :: A) [] dirs
      )
    end

fun check_targets_are_in_graph graph tgts =
    let
      fun check1 tgt =
          case target_node graph tgt of
              SOME _ => true
            | NONE => hm_target.tgtexists_readable tgt orelse
                      (warn ("Don't know how to build `" ^
                             hm_target.toString tgt ^ "'.");
                       false)
    in
      List.all check1 tgts orelse OS.Process.exit OS.Process.failure
    end

fun work() =
    case targets of
      [] => let
        val (depgraph, local_incinfo) = toplevel_build_graph()
        val targets = if cline_recursive_build then
                        get_targets_recursively local_incinfo
                      else generate_all_plausible_targets warn start_tgt
        val depgraph =
            if toplevel_no_prereqs then
              mk_dirneeded (hmdir.curdir()) (mkneeded targets depgraph)
            else
              mkneeded targets depgraph
        val _ = diag "core" (
              fn _ =>
                 let
                   fun pr t = if hm_target.tgtexists_readable t then
                                tgt_toString t
                              else tgt_toString t ^ "(*)"
                 in
                   "Generated targets are: [" ^concatWithf pr ", " targets ^ "]"
                 end
            )
        val _ = diag "core"
                     (fn _ => "Dep.graph =\n" ^ HM_DepGraph.toString depgraph)
      in
        if cline_nobuild then
          let val _ = print ("Dependency graph" ^
                             HM_DepGraph.toString depgraph ^
                             "\n\nTop-sorted:\n")
              val sorted = HM_DepGraph.topo_sort depgraph
              fun pr n =
                  case HM_DepGraph.peeknode depgraph n of
                      NONE => die ("No node " ^
                                   HM_DepGraph.node_toString n)
                    | SOME nI =>
                      case #status nI of
                          Pending {needed = true} =>
                          print (hmdir.pretty_dir (#dir nI) ^
                                 " - " ^
                                 hm_target.toString (#target nI) ^ "\n")
                        | _ => ()
              val _ = app pr sorted
          in
            OS.Process.success
          end
        else
          postmortem outputfns (build_graph depgraph)
          handle e => die ("Exception: "^General.exnMessage e)
      end
    | xs => let
        val cleanTargets =
            List.filter (fn x => member x ["clean", "cleanDeps", "cleanAll"]) xs
        fun visit_and_clean tgts d =
            let
              val _ = FileSys.chDir (hmdir.toAbsPath d)
            in
              List.app do_clean_target tgts;
              FileSys.chDir (hmdir.toAbsPath original_dir)
            end
        fun transform_thy_target s =
            if String.isSuffix "Theory" s then s ^ ".uo"
            else s
        val xs = map transform_thy_target xs
      in
        if not (null cleanTargets) then
          if not cline_recursive_clean then
            (List.app (ignore o do_clean_target) cleanTargets;
             finish_logging true;
             OS.Process.success)
          else (
            recursively getnewincs (SOME cline_incs) {
              outputfns = outputfns, verb = "Cleaning",
              hm = (fn _ => fn _ => fn _ => fn _ =>
                       List.app (ignore o do_clean_target) cleanTargets),
              dirinfo = {incdirmap=idmap0, ancestors = [original_dir],
                         visited = Binaryset.empty hmdir.compare},
              dir = original_dir,
              data = ()
            };
            OS.Process.success
          )
        else
          let
            val (depgraph, local_incinfo) = toplevel_build_graph()
            val targets = map filestr_to_tgt xs
            val depgraph =
                if toplevel_no_prereqs then
                  mk_dirneeded (hmdir.curdir()) (mkneeded targets depgraph)
                else
                  mkneeded targets depgraph
            val _ = check_targets_are_in_graph depgraph targets
          in
            if cline_nobuild then
              (print ("Dependency graph" ^ HM_DepGraph.toString depgraph);
               OS.Process.success)
            else
              postmortem outputfns (build_graph depgraph)
              handle e => die ("Exception: "^General.exnMessage e)
          end
      end

in
  if show_usage then
    print (GetOpt.usageInfo {
              header = "Usage:\n  " ^ CommandLine.name() ^ " [targets]\n\n\
                       \Special targets are: clean, cleanDeps and cleanAll\n\n\
                       \Extra options:",
              options = HM_Cline.option_descriptions
          })
  else let
      open Process
      val result = work()
          handle Fail s => die ("Fail exception: "^s^"\n")
    in
      exit result
    end

end (* main *)

end (* struct *)
\<close>



end
