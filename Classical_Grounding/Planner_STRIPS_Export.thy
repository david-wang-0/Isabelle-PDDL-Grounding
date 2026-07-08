theory Planner_STRIPS_Export
  imports Planner_STRIPS_Executable
begin

section \<open>Retained non-DFS planner (not code-exported)\<close>

text \<open>The \<^bold>\<open>single code export\<close> of the development is \<open>Planner_Export\<close>: the DFS-founded SAT planner,
  both the propositional and numeric error-monad grounders, and the plan reconstructors, all generated
  into \<^emph>\<open>one\<close> \<open>.sml\<close> file (\<open>../SMLCodebase/code/PDDL_SAT_Planner_DFS_Exported.sml\<close>, the only
  \<open>export_files\<close> clause in \<open>./ROOT\<close>).

  The non-DFS planner \<^const>\<open>plan_by_cert\<close> and its soundness (\<open>plan_by_cert_sound\<close>) remain fully proven
  in \<open>Planner_STRIPS_Executable\<close>, but --- with datalog foundedness discharged by the ordered linear
  scan (\<open>dl_founded_exec\<close>) rather than the verified directed-cycle DFS (\<open>dl_acyclic_dfs\<close>) that the
  exported \<^const>\<open>plan_by_cert_dfs\<close> uses --- it is kept for reference only and is not code-exported.\<close>

end
