theory Version
  imports Main
begin

local_setup \<open>
  let
    val version =
      trim_line (#1 (Isabelle_System.bash_output "cat $ISAFOR/../.version")) ^ " [hg: " ^
      trim_line (#1 (Isabelle_System.bash_output ("cd $ISAFOR/../ && test -d .hg && hg id -i || echo unknown"))) ^ "]"
  in
    Local_Theory.define
      ((\<^binding>\<open>version\<close>, NoSyn),
        ((\<^binding>\<open>version_def\<close>, []), HOLogic.mk_literal version)) #> #2
  end
\<close>

declare version_def [code]

end
