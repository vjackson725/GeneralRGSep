theory Locality
  imports RGLogic
begin

section \<open> Frame Locality \<close>

definition
  \<open>frame_local F p pa \<equiv>
    (\<forall>f\<le>F. (p \<^emph>\<and> f) \<sqinter> pa \<le> (p \<sqinter> pa) \<^emph>\<and> f) \<and>
    post_state (curry (p \<sqinter> pa)) \<le> post_state (curry F)\<close>


section \<open> Local Rules \<close>

lemma rgsat_if_then_else_local:
  assumes locality_assms:
    \<open>frame_local F (sswa R p) pp\<close>
    \<open>frame_local F (sswa R p) (-pp)\<close>
    and tt_guard_assm:
    \<open>sswa R p \<sqinter> pp \<le> wssa R pp \<sqinter> wssa R qa\<close>
    \<open>rel_liftL (sswa R p \<sqinter> pp) \<le> \<top> \<times>\<^sub>R G\<close>
    and ff_guard_assm:
    \<open>sswa R p \<sqinter> -pp \<le> wssa R (-pp) \<sqinter> wssa R qb\<close>
    \<open>rel_liftL (sswa R p \<sqinter> -pp) \<le> \<top> \<times>\<^sub>R G\<close>
    and body_assms:
    \<open>R, G, Ia, F, C \<turnstile> { sswa R p \<sqinter> wssa R pp } ctt { qa }\<close>
    \<open>R, G, Ib, F, C \<turnstile> { sswa R p \<sqinter> wssa R (-pp) } cff { qb }\<close>
    and misc_assms:
    \<open>C (Await pp)\<close>
    \<open>C (Await (-pp))\<close>
    \<open>C (Await pp ;; ctt)\<close>
    \<open>C (Await (- pp) ;; cff)\<close>
    \<open>C (IfThenElse pp ctt cff)\<close>
    \<open>sswa R p \<le> I\<close>
    \<open>Ia \<le> I\<close>
    \<open>Ib \<le> I\<close>
    \<open>qa \<le> q\<close>
    \<open>qb \<le> q\<close>
  shows
    \<open>R, G, I, F, C \<turnstile> { p } IfThenElse pp ctt cff { q }\<close>
  using assms
proof (intro rgsat_if_then_else[where qa=qa])
  show \<open>\<forall>f\<le>F. (sswa R p \<^emph>\<and> f) \<sqinter> pp \<le> wssa R qa \<^emph>\<and> f\<close>
    using locality_assms tt_guard_assm
    by (simp add: frame_local_def, meson order_trans sepconj_conj_monoL)
next
  show \<open>rel_liftL ((sswa R p \<^emph>\<and> F) \<sqinter> pp) \<sqinter> (=) \<le> \<top> \<times>\<^sub>R G\<close>
    using locality_assms tt_guard_assm
    by (simp add: frame_local_def post_state_def imp_ex_conjL reflp_def le_fun_def
        sepconj_conj_apply, metis)
next
  show \<open>\<forall>f\<le>F. (sswa R p \<^emph>\<and> f) \<sqinter> pp \<le> (sswa R p \<sqinter> wssa R pp) \<^emph>\<and> f\<close>
    using locality_assms tt_guard_assm
    by (clarsimp simp add: frame_local_def le_fun_def imp_ex_conjL
        sepconj_conj_apply, metis (no_types))
next
  show \<open>\<forall>f\<le>F. (sswa R p \<^emph>\<and> f) \<sqinter> - pp \<le> wssa R qb \<^emph>\<and> f\<close>
    using locality_assms ff_guard_assm
    by (simp add: frame_local_def, meson order_trans sepconj_conj_monoL)
next
  show \<open>rel_liftL ((sswa R p \<^emph>\<and> F) \<sqinter> - pp) \<sqinter> (=) \<le> \<top> \<times>\<^sub>R G\<close>
    using locality_assms ff_guard_assm
    by (simp add: frame_local_def post_state_def imp_ex_conjL reflp_def le_fun_def
        sepconj_conj_apply, metis)
next
  show \<open>\<forall>f\<le>F. (sswa R p \<^emph>\<and> f) \<sqinter> - pp \<le> (sswa R p \<sqinter> wssa R (-pp)) \<^emph>\<and> f\<close>
    using locality_assms ff_guard_assm
    by (clarsimp simp add: frame_local_def le_fun_def imp_ex_conjL
        sepconj_conj_apply, metis (no_types))
qed fast+


end