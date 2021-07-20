(* Prekernel *)

session Prekernel in Prekernel = Pure +
  theories
    Prekernel


(* Original HOL4 Kernel *)

session Core_Original in Original = Prekernel +
  theories
    Core

session More_Original in "Original/More"  = Core_Original +
  theories
    More

session Large_Original in "Original/Large"  = More_Original +
  theories
    Large

session CakeML_Deps_Original in "Original/CakeML/Deps" = More_Original +
  theories
    CakeML_Deps

session CakeML_Semantics_Original in "Original/CakeML/Semantics" = CakeML_Deps_Original +
  theories
    CakeML_Semantics

session CakeML_Translator_Original in "Original/CakeML/Translator" = CakeML_Semantics_Original +
  theories
    CakeML_Translator


(* Isabelle/HOL HOL4 Kernel *)

session Core_Isabelle in Isabelle = HOL +
  sessions
    Prekernel
  directories
    "../splice"
  theories
    Core

session More_Isabelle in "Isabelle/More"  = Core_Isabelle +
  theories
    More

session Large_Isabelle in "Isabelle/Large"  = More_Isabelle +
  theories
    Large

session CakeML_Deps_Isabelle in "Isabelle/CakeML/Deps" = More_Isabelle +
  theories
    CakeML_Deps

session CakeML_Semantics_Isabelle in "Isabelle/CakeML/Semantics" = CakeML_Deps_Isabelle +
  theories
    CakeML_Semantics

session CakeML_Translator_Isabelle in "Isabelle/CakeML/Translator" = CakeML_Semantics_Isabelle +
  theories
    CakeML_Translator

(* Debug Kernel *)

session Core_Debug in Debug = Core_Isabelle +
  sessions
    Core_Original
  theories
    Core

session More_Debug in "Debug/More"  = Core_Debug +
  theories
    More

session Large_Debug in "Debug/Large"  = More_Debug +
  theories
    Large


(*
session HOL4_Core_Isabelle = HOL +
  sessions
    HOL4_Prekernel
  theories
    HOL4_Core_Isabelle

session HOL4_Core_Debug = HOL4_Core_Isabelle +
  sessions
    HOL4_Core_Original
  theories
    HOL4_Core_Debug


(* More *)

session HOL4_More_Isabelle = HOL4_Core_Isabelle +
  theories
    HOL4_More_Isabelle

session HOL4_More_Debug = HOL4_Core_Debug +
  theories
    HOL4_More_Debug


(* Large *)

session HOL4_Large_Isabelle = HOL4_More_Isabelle +
  theories
    HOL4_Large_Isabelle

session HOL4_Large_Debug = HOL4_More_Debug +
  theories
    HOL4_Large_Debug

(* CakeML semantics *)

session CakeML_Semantics_Isabelle = HOL4_Large_Isabelle +
  theories
    CakeML_Semantics_Isabelle

session CakeML_Semantics_Original = HOL4_Large_Original +
  theories
    CakeML_Semantics_Original



(* Example *)

session Example_Transfer = HOL4_Core_Isabelle +
  theories
    Example_Transfer
*)
