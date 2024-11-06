theory Tools
  imports ML_Environment
begin

declare [[ML_environment = "HOL4"]]

ML \<open>Context_Var.bind_ref "HOL4_Tools"\<close>

ML_file "../HOL/tools/mlyacc/mlyacclib/MLY_base-sig.sml"
ML_file "../HOL/tools/mlyacc/mlyacclib/MLY_join.sml"
ML_file "../HOL/tools/mlyacc/mlyacclib/MLY_lrtable.sml"
(* Version of MLY_stream with unsychronized refs *)
ML\<open>
structure Stream :> STREAM =
struct
   open Uref
   datatype 'a str = EVAL of 'a * 'a str Uref.t | UNEVAL of (unit->'a)

   type 'a stream = 'a str Uref.t

   fun get s = (case !s of
       EVAL t => t
     | UNEVAL f =>
	    let val t = (f(), Uref.new(UNEVAL f)) in s := EVAL t; t end)

   fun streamify f = Uref.new(UNEVAL f)
   fun cons(a,s) = Uref.new(EVAL(a,s))

end;
\<close>
ML_file "../HOL/tools/mlyacc/mlyacclib/MLY_parser2.sml"

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
(*ML_file \<open>../HOL/tools-poly/Holmake/CompilerSpecific.ML\<close> 
there's an implementation but we don't we need it*)
ML_file \<open>../HOL/tools/Holmake/Systeml.sig\<close>
ML_file \<open>../HOL/tools-poly/Holmake/Systeml.sml\<close>

text\<open>Based on @{file "../HOL/tools-poly/poly-build.ML"}\<close>
subsection \<open>poly-build.ML\<close>
ML_file \<open>../HOL/tools/Holmake/GetOpt.sig\<close>
ML_file \<open>../HOL/tools/Holmake/GetOpt.sml\<close>
ML_file \<open>../HOL/tools/Holmake/HOLFS_dtype.sml\<close>
ML_file \<open>../HOL/tools/Holmake/HFS_NameMunge.sig\<close>
ML_file \<open>../HOL/tools/Holmake/HOLFileSys.sig\<close>
ML_file \<open>../HOL/tools/Holmake/HOLFileSys.sml\<close>
ML_file \<open>../HOL/tools/Holmake/Holdep_tokens.sig\<close>
ML_file \<open>../HOL/tools/Holmake/Holdep_tokens.sml\<close>
ML_file \<open>../HOL/tools/Holmake/HM_SimpleBuffer.sig\<close>
ML_file \<open>../HOL/tools/Holmake/HM_SimpleBuffer.sml\<close>
ML_file \<open>../HOL/tools/Holmake/AttributeSyntax.sig\<close>
ML_file \<open>../HOL/tools/Holmake/AttributeSyntax.sml\<close>
ML_file \<open>../HOL/tools/Holmake/QuoteFilter.sml\<close>
ML_file \<open>../HOL/tools/Holmake/QFRead.sig\<close>
ML_file \<open>../HOL/tools/Holmake/QFRead.sml\<close>
ML_file \<open>../HOL/tools/Holmake/Holdep.sig\<close>
ML_file \<open>../HOL/tools/Holmake/Holdep.sml\<close>
ML_file \<open>../HOL/tools/Holmake/Holmake_tools_dtype.sml\<close>
ML_file \<open>../HOL/tools/Holmake/terminal_primitives.sig\<close>
(* We're not in a terminal
ML_file \<open>../HOL/tools/Holmake/poly-terminal-prims.ML\<close>*)

ML\<open>
structure terminal_primitives :> terminal_primitives =
struct
(*TODO figure out what this is for*)
fun strmIsTTY (outstream : TextIO.outstream) = false

fun TERM_isANSI () = false

end\<close>
ML_file \<open>../HOL/tools/Holmake/Holmake_tools.sig\<close>
ML_file \<open>../HOL/tools/Holmake/Holmake_tools.sml\<close>
ML_file \<open>../HOL/tools/Holmake/regexpMatch.sig\<close>
ML_file \<open>../HOL/tools/Holmake/regexpMatch.sml\<close>
ML_file \<open>../HOL/tools/Holmake/parse_glob.sig\<close>
ML_file \<open>../HOL/tools/Holmake/parse_glob.sml\<close>
ML_file \<open>../HOL/tools/Holmake/internal_functions.sig\<close>
ML_file \<open>../HOL/tools/Holmake/internal_functions.sml\<close>
ML_file \<open>../HOL/tools/Holmake/Holmake_types.sig\<close>
ML_file \<open>../HOL/tools/Holmake/Holmake_types.sml\<close>
ML_file \<open>../HOL/tools/Holmake/ReadHMF.sig\<close>
ML_file \<open>../HOL/tools/Holmake/ReadHMF.sml\<close>
ML_file \<open>../HOL/tools/buildcline_dtype.sml\<close>
ML_file \<open>../HOL/tools/Holmake/FunctionalRecordUpdate.sml\<close>
ML_file \<open>../HOL/tools/buildcline.sig\<close>
ML_file \<open>../HOL/tools/buildcline.sml\<close>




(*
ML_file "../HOL/tools/Holmake/SourcePos.sig"
ML_file "../HOL/tools/Holmake/SourcePos.sml"
ML_file "../HOL/tools/Holmake/tailbuffer.sig"
ML_file "../HOL/tools/Holmake/tailbuffer.sml"

ML_file "../HOL/tools/Holmake/SourceFile.sig"
ML_file "../HOL/tools/Holmake/SourceFile.sml"*)
ML \<open>structure Holmake_tools : Holmake_tools = struct
  open Holmake_tools
  fun getWidth () = 80
end\<close>
(*
ML_file "../HOL/tools/Holmake/HM_Core_Cline.sig"
ML_file "../HOL/tools/Holmake/HM_Core_Cline.sml"
ML_file "../HOL/tools/Holmake/HM_DepGraph.sig"
ML_file "../HOL/tools/Holmake/HM_DepGraph.sml"
ML_file "../HOL/tools/Holmake/holdeptool.sml"

ML_file "../HOL/tools/Holmake/HM_GraphBuildJ1.sig"
ML_file "../HOL/tools/Holmake/HM_GraphBuildJ1.sml"
ML_file "../HOL/tools/Holmake/poly/HM_Cline.sig"
ML_file "../HOL/tools/Holmake/poly/HM_Cline.sml"
ML_file "../HOL/tools/Holmake/poly/HM_BaseEnv.sig"
ML_file "../HOL/tools/Holmake/poly/HM_BaseEnv.sml"
ML_file "../HOL/tools/Holmake/poly/GraphExtra.sig"
ML_file "../HOL/tools/Holmake/poly/GraphExtra.sml"
ML_file "../HOL/tools/Holmake/BuildCommand.sig"


ML \<open>structure CompilerSpecific :>
  sig
    val quietbind : string -> unit
  end =
struct

fun quietbind s =
  ML_Compiler.eval {debug = NONE, environment="HOL4", redirect = false, verbose = false, catch_all = true,
  warning = fn _ => (), writeln = fn _ => ()} Position.none (ML_Lex.tokenize s)
end
\<close> \<comment> \<open>not
ML_file "../HOL/tools-poly/Holmake/CompilerSpecific.ML"
\<close>*)

end
