theory Soundness
  imports RGLogic
begin


section \<open> Operational Semantics \<close>

type_synonym 's pconfig = \<open>'s \<times> 's comm\<close>


subsection \<open> Actions \<close>

datatype act = Tau | Vis

lemma act_not_eq_iff[simp]:
  \<open>\<alpha> \<noteq> Tau \<longleftrightarrow> \<alpha> = Vis\<close>
  \<open>\<alpha> \<noteq> Vis \<longleftrightarrow> \<alpha> = Tau\<close>
  by (meson act.distinct act.exhaust)+

lemma ex_act_eq[simp]:
  \<open>\<exists>\<alpha>. \<alpha> = Vis\<close>
  \<open>\<exists>\<alpha>. \<alpha> = Tau\<close>
  \<open>\<exists>\<alpha>. \<alpha> \<noteq> Vis\<close>
  \<open>\<exists>\<alpha>. \<alpha> \<noteq> Tau\<close>
  by blast+

lemma all_act_eq[simp]:
  \<open>(\<forall>\<alpha>. \<alpha> = Vis) \<longleftrightarrow> False\<close>
  \<open>(\<forall>\<alpha>. \<alpha> = Tau) \<longleftrightarrow> False\<close>
  \<open>(\<forall>\<alpha>. \<alpha> \<noteq> Vis) \<longleftrightarrow> False\<close>
  \<open>(\<forall>\<alpha>. \<alpha> \<noteq> Tau) \<longleftrightarrow> False\<close>
  by blast+

lemma all_act_iff:
  \<open>All p \<longleftrightarrow> p Tau \<and> p Vis\<close>
  by (metis act_not_eq_iff(1))

lemma ex_act_iff:
  \<open>Ex p \<longleftrightarrow> p Tau \<or> p Vis\<close>
  by (metis act_not_eq_iff(2))


subsection \<open> Operational semantics steps \<close>

fun opstep :: \<open>act \<Rightarrow> 's pconfig \<Rightarrow> 's pconfig \<Rightarrow> bool\<close> where
  \<open>opstep \<alpha> (s, Skip) sc' \<longleftrightarrow> False\<close>
| \<open>opstep \<alpha> (s, ca ;; cb) sc' \<longleftrightarrow>
    \<alpha> = Tau \<and> ca = Skip \<and> sc' = (s, cb) \<or>
    (\<exists>s' ca'. opstep \<alpha> (s, ca) (s', ca') \<and> sc' = (s', ca' ;; cb))\<close>
| \<open>opstep \<alpha> (s, ca \<^bold>\<sqinter> cb) sc' \<longleftrightarrow>
    \<alpha> = Tau \<and> sc' = (s, ca) \<or>
    \<alpha> = Tau \<and> sc' = (s, cb)\<close>
| \<open>opstep \<alpha> (s, ca \<^bold>\<box> cb) sc' \<longleftrightarrow>
    \<alpha> = Tau \<and> ca = Skip \<and> sc' = (s, cb) \<or>
    \<alpha> = Tau \<and> cb = Skip \<and> sc' = (s, ca) \<or>
    \<alpha> = Tau \<and> (\<exists>s' ca'. sc' = (s', ca' \<^bold>\<box> cb) \<and> opstep Tau (s, ca) (s', ca')) \<or>
    \<alpha> = Tau \<and> (\<exists>s' cb'. sc' = (s', ca \<^bold>\<box> cb') \<and> opstep Tau (s, cb) (s', cb')) \<or>
    \<alpha> \<noteq> Tau \<and> opstep \<alpha> (s, ca) sc' \<or>
    \<alpha> \<noteq> Tau \<and> opstep \<alpha> (s, cb) sc'\<close>
| \<open>opstep \<alpha> (s, ca \<parallel> cb) sc' \<longleftrightarrow>
    \<alpha> = Tau \<and> ca = Skip \<and> cb = Skip \<and> sc' = (s, Skip) \<or>
    (\<exists>s' ca'. opstep \<alpha> (s, ca) (s', ca') \<and> sc' = (s', ca' \<parallel> cb)) \<or>
    (\<exists>s' cb'. opstep \<alpha> (s, cb) (s', cb') \<and> sc' = (s', ca \<parallel> cb'))\<close>
| \<open>opstep \<alpha> (s, DO c OD) sc' \<longleftrightarrow>
    \<alpha> = Tau \<and> (\<forall>\<alpha>' sc'. \<not> opstep \<alpha>' (s, c) sc') \<and> sc' = (s, Skip) \<or>
    (\<exists>s' c'. opstep \<alpha> (s, c) (s', c') \<and> sc' = (s', c' ;; DO c OD))\<close>
| \<open>opstep \<alpha> (s, Atomic ar) sc' \<longleftrightarrow>
    \<alpha> = Vis \<and> ar s (fst sc') \<and> snd sc' = Skip\<close>

lemmas opstep_induct =
  opstep.induct[case_names Skip Seq Indet Endet Par DoLoop Atom]


paragraph \<open> Pretty operational semantics \<close>

abbreviation pretty_opstep :: \<open>_ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> _\<close> (\<open>_ \<midarrow>(_)\<rightarrow> _\<close> [60,0,60] 60) where
  \<open>sc \<midarrow>\<alpha>\<rightarrow> msc' \<equiv> opstep \<alpha> sc msc'\<close>

definition pretty_no_opstep :: \<open>_ \<Rightarrow> bool\<close> (\<open>_ \<midarrow>'/\<rightarrow>\<close> [60] 60) where
  \<open>sc \<midarrow>/\<rightarrow> \<equiv> \<forall>\<alpha> sc'. \<not> opstep \<alpha> sc sc'\<close>

abbreviation \<open>\<B> c s \<equiv> (s, c) \<midarrow>/\<rightarrow>\<close>

lemma opstep_simp_loop[simp]:
  \<open>opstep \<alpha> (s, DO c OD) sc' \<longleftrightarrow>
    \<alpha> = Tau \<and> (s, c) \<midarrow>/\<rightarrow> \<and> sc' = (s, Skip) \<or>
    (\<exists>s' c'. opstep \<alpha> (s, c) (s', c') \<and> sc' = (s', c' ;; DO c OD))\<close>
  by (simp add: pretty_no_opstep_def)

declare opstep.simps(6)[simp del]

lemma pretty_no_opstep_simps[simp]:
  \<open>(s, Skip) \<midarrow>/\<rightarrow>\<close>
  \<open>(s, ca ;; cb) \<midarrow>/\<rightarrow> \<longleftrightarrow> ca \<noteq> Skip \<and> (s, ca) \<midarrow>/\<rightarrow>\<close>
  \<open>(s, ca \<^bold>\<sqinter> cb) \<midarrow>/\<rightarrow> \<longleftrightarrow> False\<close>
  \<open>(s, ca \<^bold>\<box> cb) \<midarrow>/\<rightarrow> \<longleftrightarrow> ca \<noteq> Skip \<and> cb \<noteq> Skip \<and> (s, ca) \<midarrow>/\<rightarrow> \<and> (s, cb) \<midarrow>/\<rightarrow>\<close>
  \<open>(s, ca \<parallel> cb) \<midarrow>/\<rightarrow> \<longleftrightarrow> (cb \<noteq> Skip \<or> ca \<noteq> Skip) \<and> (s, ca) \<midarrow>/\<rightarrow> \<and> (s, cb) \<midarrow>/\<rightarrow>\<close>
  \<open>(s, DO c OD) \<midarrow>/\<rightarrow> \<longleftrightarrow> False\<close>
  \<open>(s, \<langle> ar \<rangle>) \<midarrow>/\<rightarrow> \<longleftrightarrow> (\<nexists>s'. ar s s')\<close>
  by (simp add: pretty_no_opstep_def all_act_iff all_conj_distrib; fastforce)+


subsection \<open> Lemmas about opstep \<close>

lemma opstep_tau_preserves_state:
  assumes \<open>s \<midarrow>Tau\<rightarrow> s'\<close>
  shows \<open>fst s' = fst s\<close>
proof -
  { fix \<alpha>
    have \<open>s \<midarrow>\<alpha>\<rightarrow> s' \<Longrightarrow> \<alpha> = Tau \<Longrightarrow> fst s' = fst s\<close>
      by (induct \<alpha> s s' rule: opstep.induct) (force split: if_splits)+
  }
  then show ?thesis
    using assms by force
qed

lemma vis_step_impl_atom:
  assumes \<open>(s, c) \<midarrow>Vis\<rightarrow> (s', c')\<close>
  shows \<open>\<exists>ar. ar \<in># head_atoms c \<and> ar s s'\<close>
proof -
  { fix \<alpha> sc sc'
    have
      \<open>sc \<midarrow>\<alpha>\<rightarrow> sc' \<Longrightarrow>
        sc = (s, c) \<Longrightarrow>
        sc' = (s', c') \<Longrightarrow>
        \<alpha> = Vis \<Longrightarrow>
        \<exists>ar. ar \<in># head_atoms c \<and> ar s s'\<close>
      by (induct \<alpha> sc sc' arbitrary: c s s' c' rule: opstep.induct)
        fastforce+
  }
  then show ?thesis
    using assms
    by blast
qed

lemma opstep_act_cases:
  \<open>s \<midarrow>\<alpha>\<rightarrow> s' \<Longrightarrow>
    (\<alpha> = Tau \<Longrightarrow> s \<midarrow>Tau\<rightarrow> s' \<Longrightarrow> fst s' = (fst s) \<Longrightarrow> P) \<Longrightarrow>
    (\<alpha> = Vis \<Longrightarrow> s \<midarrow>Vis\<rightarrow> s' \<Longrightarrow> P) \<Longrightarrow>
    P\<close>
  by (metis (full_types) act.exhaust opstep_tau_preserves_state)


text \<open>
  It would be nice if a tau-move happening did not depend on the state.
  However, this is not the case, as do loops may exit based on whether the subcommand is blocked
  or not. This exit produced a tau-step.
\<close>
lemma tau_opstep_state_irrelevant:
  \<comment> \<open> False because of do loops \<close>
  \<open>sc \<midarrow>\<alpha>\<rightarrow> sc' \<Longrightarrow>
    \<alpha> = Tau \<Longrightarrow>
    (sx, snd sc) \<midarrow>\<alpha>\<rightarrow> (sx, snd sc')\<close>
proof (induct _ sc sc' arbitrary: sx rule: opstep_induct)
  case (DoLoop l\<alpha> s c sc')
  then show ?case
    (* This subgoal fails *)
    oops


subsubsection \<open> adding parallel \<close>

lemma opstep_parallel_leftD:
  \<open>s \<midarrow>\<alpha>\<rightarrow> s' \<Longrightarrow> (fst s, snd s \<parallel> cy) \<midarrow>\<alpha>\<rightarrow> (fst s', snd s' \<parallel> cy)\<close>
  by simp

lemma opstep_parallel_rightD:
  \<open>s \<midarrow>\<alpha>\<rightarrow> s' \<Longrightarrow> (fst s, cx \<parallel> snd s) \<midarrow>\<alpha>\<rightarrow> (fst s', cx \<parallel> snd s')\<close>
  by simp


subsubsection \<open> Interaction with map_comm \<close>

lemma opstep_preserves_map_atom:
  \<open>(s, map_atom f c) \<midarrow>\<alpha>\<rightarrow> (s', cx') \<Longrightarrow> \<exists>c'. cx' = map_atom f c'\<close>
  apply (induct c arbitrary: cx')
        apply force
       apply clarsimp
       apply (metis map_atom.simps(2))
      apply (clarsimp simp add: map_atom_rev_iff)
      apply (metis (full_types) map_atom.simps(1,3))
     apply clarsimp
     apply (elim disjE; blast?; metis map_atom.simps(5))
    apply clarsimp
    apply (elim disjE)
         apply force
        apply force
       apply (metis map_atom_rev_iff(5))
      apply (metis map_atom_rev_iff(5))
     apply force
    apply force
   apply (simp add: map_atom_rev_iff2; fail)
  apply clarsimp
  apply (elim disjE)
   apply (metis map_atom.simps(1))
  apply (metis map_atom_rev_iff2(2,6))
  done


subsection \<open> opstep + subcommand collectors \<close>

\<comment> \<open> set, not msets, as loops increase the atoms. \<close>
lemma opstep_subcomm_atoms_set_mono:
  fixes s :: 's
    and c :: \<open>'s comm\<close>
  assumes  \<open>(s, c) \<midarrow>\<alpha>\<rightarrow> (s', c')\<close>
  shows \<open>set_mset (subcomm_atoms c') \<subseteq> set_mset (subcomm_atoms c)\<close>
proof -
  { fix sc sc' :: \<open>'s \<times> 's comm\<close>
    have \<open>opstep \<alpha> sc sc' \<Longrightarrow> set_mset (subcomm_atoms (snd sc')) \<subseteq> set_mset (subcomm_atoms (snd sc))\<close>
      by (induct \<alpha> sc sc' rule: opstep.induct) fastforce+
  }
  then show ?thesis
    using assms
    by (metis snd_conv)
qed

lemma opstep_preserves_all_atom_comm:
  \<open>opstep \<alpha> (h, c) (h', c') \<Longrightarrow> all_atoms p c \<le> all_atoms p c'\<close>
  using opstep_subcomm_atoms_set_mono
  by (force intro: Inf_mono simp add: all_atoms_def)

lemmas opstep_preserves_all_atom_comm_rev = opstep_preserves_all_atom_comm[rotated]

lemma opstep_preserves_all_loops_all_head_atoms:
  \<open>(s, c) \<midarrow>\<alpha>\<rightarrow> (s', c') \<Longrightarrow> all_loops (all_head_atoms p) c \<le> all_loops (all_head_atoms p) c'\<close>
  apply (induct c arbitrary: \<alpha> s' c')
        apply force
       apply clarsimp
       apply (fastforce dest: inf_mono)
      apply clarsimp
      apply (elim disjE)
        apply force
       apply (metis all_loops_simps(5) inf_mono order_eq_refl)
      apply (metis all_loops_simps(5) inf_mono order_eq_refl)
     apply force
    apply clarsimp
    apply (elim disjE)
         apply force
        apply force
       apply (metis all_loops_simps(4) inf_mono order_eq_refl)
      apply (metis all_loops_simps(4) inf_mono order_eq_refl)
     apply (blast dest: le_infI1)
    apply (blast dest: le_infI2)
   apply force
  apply clarsimp
  apply (elim disjE)
   apply force
  apply (force dest: le_infI2)
  done

lemmas opstep_preserves_all_loops_all_atoms_rev =
  opstep_preserves_all_loops_all_head_atoms[rotated]


section \<open> Opstep rules for defined programs \<close>

paragraph \<open> Await \<close>

lemma opstep_await_iff[simp]:
  \<open>opstep \<alpha> (s, Await p) sc' \<longleftrightarrow>
    \<alpha> = Vis \<and> p s \<and> sc' = (s, Skip)\<close>
  by (cases sc', force simp add: await_rel_def)


paragraph \<open> IfThenElse \<close>

lemma opstep_IfThenElse_iff[simp]:
  \<open>opstep \<alpha> (s, IfThenElse p ct cf) sc' \<longleftrightarrow>
    \<alpha> = Vis \<and>
    (p s \<and> sc' = (s, Skip ;; ct) \<or>
      \<not> p s \<and> sc' = (s, Skip ;; cf))\<close>
  by (cases sc', force simp add: IfThenElse_def await_rel_def)

lemma opstep_WhileLoop_iff[simp]:
  \<open>opstep \<alpha> (h, WhileLoop p c) s' \<longleftrightarrow>
    \<alpha> \<noteq> Tau \<and> p h \<and> s' = (h, (Skip ;; c) ;; DO Await p ;; c OD) \<or>
    \<alpha> = Tau \<and> \<not> p h \<and> s' = (h, Skip)\<close>
  by (force simp add: WhileLoop_def await_rel_def pre_state_def pretty_no_opstep_def)


section \<open> Self-opstep Impossible \<close>

lemma comm_self_containment_impossible[simp]:
  \<open>c1 ;; c2 \<le> c1 \<longleftrightarrow> False\<close>
  \<open>c1 ;; c2 \<le> c2 \<longleftrightarrow> False\<close>
  \<open>c1 \<parallel> c2 \<le> c1 \<longleftrightarrow> False\<close>
  \<open>c1 \<parallel> c2 \<le> c2 \<longleftrightarrow> False\<close>
  \<open>c1 \<^bold>\<sqinter> c2 \<le> c1 \<longleftrightarrow> False\<close>
  \<open>c1 \<^bold>\<sqinter> c2 \<le> c2 \<longleftrightarrow> False\<close>
  \<open>c1 \<^bold>\<box> c2 \<le> c1 \<longleftrightarrow> False\<close>
  \<open>c1 \<^bold>\<box> c2 \<le> c2 \<longleftrightarrow> False\<close>
  \<open>DO c OD \<le> c \<longleftrightarrow> False\<close>
  using less_comm_simps_right
  by (fastforce dest: leD)+

inductive endet_expansion :: \<open>'a comm \<Rightarrow> 'a comm \<Rightarrow> bool\<close> where
  eexp_reflI[intro!]: \<open>endet_expansion c c\<close>
| eexp_leftI[intro]: \<open>endet_expansion c ca \<Longrightarrow> endet_expansion c (ca \<^bold>\<box> cb)\<close>
| eexp_rightI[intro]: \<open>endet_expansion c cb \<Longrightarrow> endet_expansion c (ca \<^bold>\<box> cb)\<close>

inductive_cases endet_expansion_right_SkipE[elim!]: \<open>endet_expansion c Skip\<close>
inductive_cases endet_expansion_right_SeqE[elim!]: \<open>endet_expansion c (ca ;; cb)\<close>
inductive_cases endet_expansion_right_IndetE[elim!]: \<open>endet_expansion c (ca \<^bold>\<sqinter> cb)\<close>
inductive_cases endet_expansion_right_EndetE[elim]: \<open>endet_expansion c (ca \<^bold>\<box> cb)\<close>
inductive_cases endet_expansion_right_ParE[elim!]: \<open>endet_expansion c (ca \<parallel> cb)\<close>
inductive_cases endet_expansion_right_AtomE[elim!]: \<open>endet_expansion c \<langle>ar\<rangle>\<close>
inductive_cases endet_expansion_right_IterE[elim!]: \<open>endet_expansion c (DO cx OD)\<close>

lemma endet_expansion_subcomm_antisym:
  \<open>endet_expansion ca cb \<Longrightarrow> cb \<le> ca \<Longrightarrow> ca = cb\<close>
  apply (induct cb arbitrary: ca)
        apply force
       apply force
      apply force
     apply force
    apply (metis comm_self_containment_impossible(7,8) less_eq_comm_leftD(7,8)
      endet_expansion_right_EndetE)
   apply force
  apply force
  done

lemma endet_expansion_indet_left[simp]:
  \<open>endet_expansion (c ;; cb) c = False\<close>
  \<open>endet_expansion (ca ;; c) c = False\<close>
  \<open>endet_expansion (c \<parallel> cb) c = False\<close>
  \<open>endet_expansion (ca \<parallel> c) c = False\<close>
  \<open>endet_expansion (c \<^bold>\<sqinter> cb) c = False\<close>
  \<open>endet_expansion (ca \<^bold>\<sqinter> c) c = False\<close>
  \<open>endet_expansion (c \<^bold>\<box> cb) c = False\<close>
  \<open>endet_expansion (ca \<^bold>\<box> c) c = False\<close>
  \<open>endet_expansion (DO c OD) c = False\<close>
  using endet_expansion_subcomm_antisym
  by fastforce+

lemma endet_expansion_endet_leftD:
  \<open>endet_expansion (ca \<^bold>\<box> cb) c' \<Longrightarrow> endet_expansion ca c'\<close>
  \<open>endet_expansion (ca \<^bold>\<box> cb) c' \<Longrightarrow> endet_expansion cb c'\<close>
  by (induct c') blast+

lemma self_opstep_endet_cluster_then_crash:
  \<open>endet_expansion c c' \<Longrightarrow> (s, c) \<midarrow>\<alpha>\<rightarrow> (s', c') \<Longrightarrow> False\<close>
proof (induct c arbitrary: \<alpha> c')
  case (Endet c1 c2)
  then show ?case
    by (clarsimp, metis comm.inject(4) eexp_reflI endet_expansion_right_EndetE
        endet_expansion_endet_leftD(1,2) endet_expansion_indet_left(7,8))
qed force+

lemmas self_opstep_endet_cluster_then_crashD = 
  self_opstep_endet_cluster_then_crash[rotated]

lemma self_opstep_impossible:
  \<open>(s, c) \<midarrow>\<alpha>\<rightarrow> (s', c) = False\<close>
  \<open>(s, c1) \<midarrow>\<alpha>\<rightarrow> (s', c1 \<^bold>\<box> c2) = False\<close>
  \<open>(s, c2) \<midarrow>\<alpha>\<rightarrow> (s', c1 \<^bold>\<box> c2) = False\<close>
  by (force dest: self_opstep_endet_cluster_then_crashD)+

lemma opstep_endet_skip_then:
  \<open>(s, c \<^bold>\<box> Skip) \<midarrow>\<alpha>\<rightarrow> (s', c) \<Longrightarrow> \<alpha> = Tau \<and> s' = s\<close>
  \<open>(s, Skip \<^bold>\<box> c) \<midarrow>\<alpha>\<rightarrow> (s', c) \<Longrightarrow> \<alpha> = Tau \<and> s' = s\<close>
  by (simp add: self_opstep_impossible, metis fst_conv opstep_tau_preserves_state)+


subsection \<open> Stable and Vis-step Enabled Commands \<close>

definition
  \<open>vis_enabled_comm c \<equiv> \<lambda>s. (\<exists>\<alpha> sc'. \<alpha> \<noteq> Tau \<and> (s, c) \<midarrow>\<alpha>\<rightarrow> sc')\<close>

lemma vis_enabled_comm_simps[simp]:
  \<open>vis_enabled_comm Skip = \<bottom>\<close>
  \<open>vis_enabled_comm (ca ;; cb) = vis_enabled_comm ca\<close>
  \<open>vis_enabled_comm (ca \<parallel> cb) = (vis_enabled_comm ca \<squnion> vis_enabled_comm cb)\<close>
  \<open>vis_enabled_comm (ca \<^bold>\<box> cb) = (vis_enabled_comm ca \<squnion> vis_enabled_comm cb)\<close>
  \<open>vis_enabled_comm (ca \<^bold>\<sqinter> cb) = \<bottom>\<close>
  \<open>vis_enabled_comm \<langle> a \<rangle> = (\<lambda>s. \<exists>s'. a s s')\<close>
  \<open>vis_enabled_comm (DO ca OD) = vis_enabled_comm ca\<close>
  by (clarsimp simp add: vis_enabled_comm_def fun_eq_iff ex_disj_distrib)+

lemma vis_enabled_comm_eq_any_head_atom_enabled:
  \<open>vis_enabled_comm c = any_head_atom (\<lambda>a s. Ex (a s)) c\<close>
  by (induct c) force+


definition
  \<open>stable_comm c \<equiv> \<lambda>s. (\<forall>sc'. \<not> (s, c) \<midarrow>Tau\<rightarrow> sc')\<close>

lemma stable_comm_simps[simp]:
  \<open>stable_comm Skip = \<top>\<close>
  \<open>stable_comm (ca ;; cb) = (if ca \<noteq> Skip then stable_comm ca else \<bottom>)\<close>
  \<open>stable_comm (ca \<parallel> cb) = (if ca \<noteq> Skip \<or> cb \<noteq> Skip then stable_comm ca \<sqinter> stable_comm cb else \<bottom>)\<close>
  \<open>stable_comm (ca \<^bold>\<box> cb) = (if ca \<noteq> Skip \<and> cb \<noteq> Skip then stable_comm ca \<sqinter> stable_comm cb else \<bottom>)\<close>
  \<open>stable_comm (ca \<^bold>\<sqinter> cb) = \<bottom>\<close>
  \<open>stable_comm \<langle> a \<rangle> = \<top>\<close>
  \<open>stable_comm (DO ca OD) = vis_enabled_comm ca \<sqinter> stable_comm ca\<close>
  by (simp add: stable_comm_def vis_enabled_comm_def pretty_no_opstep_def
      ex_act_iff all_conj_distrib; blast)+

lemmas any_head_atom_pre_state_helper =
  arg_cong2[OF ext refl, where f=any_head_atom and a=pre_state and b=\<open>\<lambda>r x. Ex (r x)\<close>,
      simplified pre_state_def, simplified]

lemma head_atomic_iff_all_stable:
  \<open>head_atomic c \<longleftrightarrow> All (stable_comm c)\<close>
  by (induct c)
    (simp add: vis_enabled_comm_eq_any_head_atom_enabled any_head_atom_pre_state_helper; fast)+

lemma vis_enabled_comm_map_atom_surj_eq[simp]:
  \<open>surj f \<Longrightarrow> vis_enabled_comm (map_atom (\<lambda>a. a \<circ>\<^sub>2 f) c) = vis_enabled_comm c \<circ> f\<close>
proof (induct c)
  case (Atomic r)
  then show ?case
    apply (clarsimp simp add: fun_eq_iff)
    apply (intro iffI; elim exE)
     apply (rename_tac x x')
     apply (rule_tac x=\<open>f x'\<close> in exI)
     apply blast
    apply (metis surj_def)
    done
qed (force simp add: map_atom_rev_iff)+

lemma stable_comm_map_atom_surj_eq[simp]:
  \<open>surj f \<Longrightarrow> stable_comm (map_atom (\<lambda>a. a \<circ>\<^sub>2 f) c) = stable_comm c \<circ> f\<close>
  by (induct c) (force simp add: map_atom_rev_iff)+


lemma head_atomic_implies_all_opstep_vis:
  \<open>sc \<midarrow>\<alpha>\<rightarrow> sc' \<Longrightarrow> head_atomic (snd sc) \<Longrightarrow> \<alpha> \<noteq> Tau\<close>
  by (cases sc, cases sc', cases \<alpha>;
      clarsimp simp add: head_atomic_iff_all_stable stable_comm_def)


subsection \<open> Any Head Guard \<close>

abbreviation \<open>any_head_guard \<equiv> any_head_atom pre_state\<close>


lemma pass_head_guard_then_some_vis_opstep:
  \<open>any_head_guard c s \<Longrightarrow> \<exists>\<alpha> sc'. (s, c) \<midarrow>\<alpha>\<rightarrow> sc' \<and> \<alpha> \<noteq> Tau\<close>
  by (induct c) (force simp add: pre_state_def)+

lemma stable_comm_then_any_head_guard_iff_not_blocked:
  \<open>stable_comm c s \<Longrightarrow> any_head_guard c s \<longleftrightarrow> \<not> (s, c) \<midarrow>/\<rightarrow>\<close>
proof (induct c)
  case (Iter c)
  then show ?case
    by (simp add: pretty_no_opstep_def vis_enabled_comm_def, blast)
qed (force simp add: pre_state_def split: if_splits)+

lemma head_atomic_then_any_head_guard_eq_not_blocked:
  \<open>head_atomic c \<Longrightarrow> any_head_guard c = (\<lambda>s. \<not> (s, c) \<midarrow>/\<rightarrow>)\<close>
  by (clarsimp simp add: fun_eq_iff)
    (metis head_atomic_iff_all_stable stable_comm_then_any_head_guard_iff_not_blocked)


section \<open> Safe \<close>

text \<open>
  The inductive predicate \<open>safe\<close> defines a tree semantics of our program \<open>c\<close>.
  It considers all executions from \<open>s\<close>, which include environment steps specified by \<open>R\<close>,
  and local \<open>opsteps\<close> from the current state (for which the state is framed by some frame in \<open>F\<close>).
    It enforces that all reachable states (from the view of the current process) must obey the
  state invariant \<open>I\<close> and all local steps must fulfil the guarantee condition \<open>G\<close>. 
  In addition, if the execution terminates, the final state must uphold the postcondition \<open>q\<close>.
\<close>
inductive safe
  :: \<open>('s \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow>
      ('l \<times> 's \<Rightarrow> bool) \<Rightarrow>
      ('s \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow>
      ('l \<times> 's \<Rightarrow> bool) \<Rightarrow>
      ('l \<times> 's \<Rightarrow> bool) \<Rightarrow>
      nat \<Rightarrow>
      ('l::pre_perm_alg \<times> 's) comm \<Rightarrow>
      'l \<times> 's \<Rightarrow>
      bool\<close>
  for R F G I q
  where safeI[intro]:
    \<open>\<comment> \<open> If the command is Skip, the postcondition is established.
        Note: this semantics represents termination by infinite final stuttering. \<close>
    (c = Skip \<longrightarrow> q s) \<Longrightarrow>
    \<comment> \<open> the current state obeys the state invariant \<close>
    I s \<Longrightarrow>
    \<comment> \<open> rely steps are safe \<close>
    (\<And>n' ss'. n = Suc n' \<Longrightarrow> R (snd s) ss' \<Longrightarrow> safe R F G I q n' c (fst s, ss')) \<Longrightarrow>
    \<comment> \<open> Safe is closed under framed opsteps: \<close>
    (\<And>n' fs \<alpha> lfs' ss' c'.
      n = Suc n' \<Longrightarrow>
      ((fst s + fs, snd s), c) \<midarrow>\<alpha>\<rightarrow> ((lfs', ss'), c') \<Longrightarrow>
      fst s ## fs \<Longrightarrow>
      F (fs, snd s) \<Longrightarrow>
      \<comment> \<open> Note that non-tau steps establish the guarantee, \<close>
      (\<alpha> \<noteq> Tau \<longrightarrow> G (snd s) ss') \<and>
        \<comment> \<open> Note the existential! We only guarantee \<^emph>\<open>one\<close> such unframed state is safe.
             There can be multiple such unframed states when the resource algebra is non-cancellative.
             When there are multiple such unframed states, the state chosen depends on the predicates
             in the subproof. As we will only prove soundness, this is enough; if we wanted to prove
             completeness, we would likely need more structure here. \<close>
        (\<exists>ls'.
          ls' ## fs \<and>  \<comment> \<open> note we require preservation of separation from the \<^emph>\<open>whole\<close> frame. \<close>
          lfs' = ls' + fs \<and>
          (\<alpha> = Tau \<longrightarrow> ls' = fst s) \<and> \<comment> \<open> Tau moves are not allowed to change the fictive state! \<close>
          safe R F G I q n' c' (ls', ss'))) \<Longrightarrow>
    \<comment> \<open> conclude a step can be made \<close>
    safe R F G I q n c s\<close>


subsection \<open> Proofs about safe \<close>

inductive_cases safe_zeroE[elim!]: \<open>safe R F G I q 0 c s\<close>
inductive_cases safe_sucE[elim]: \<open>safe R F G I q (Suc n) c s\<close>

lemma safe_then_state_inv:
  assumes \<open>safe R F G I q n c s\<close>
  shows \<open>I s\<close>
  using assms
  by (induct rule: safe.inducts) blast+

lemma safe_then_postcond:
  assumes \<open>safe R F G I q n c s\<close>
  shows \<open>c = Skip \<longrightarrow> q s\<close>
  using assms
  by (induct rule: safe.inducts) blast+


lemma safe_nil_iff[simp]:
  \<open>safe R F G I q 0 c s \<longleftrightarrow> (c = Skip \<longrightarrow> q s) \<and> I s\<close>
  by blast

lemma safe_suc_iff:
  \<open>safe R F G I q (Suc n) c s \<longleftrightarrow>
    (c = Skip \<longrightarrow> q s) \<and>
    I s \<and>
    (\<forall>ss'. R (snd s) ss' \<longrightarrow> safe R F G I q n c (fst s, ss')) \<and>
    (\<forall>\<alpha> lfs' ss' fs c'.
      ((fst s + fs, snd s), c) \<midarrow>\<alpha>\<rightarrow> ((lfs', ss'), c') \<longrightarrow>
      fst s ## fs \<longrightarrow>
      F (fs, snd s) \<longrightarrow>
      (\<alpha> \<noteq> Tau \<longrightarrow> G (snd s) ss') \<and>
        (\<exists>ls'.
          ls' ## fs \<and>
          lfs' = ls' + fs \<and>
          (\<alpha> = Tau \<longrightarrow> ls' = fst s) \<and>
          safe R F G I q n c' (ls', ss')))\<close>
  apply (rule iffI)
   apply (elim safe_sucE; simp; fail)
  apply (rule safeI; force)
  done

lemma safe_sucD:
  \<open>safe R F G I q (Suc n) c s \<Longrightarrow> R ss ss' \<Longrightarrow> ss = snd s \<Longrightarrow> safe R F G I q n c (fst s, ss')\<close>
  \<open>safe R F G I q (Suc n) c s \<Longrightarrow>
    ((fst s + fs, snd s), c) \<midarrow>\<alpha>\<rightarrow> ((slf', ss'), c') \<Longrightarrow>
    fst s ## fs \<Longrightarrow>
    F (fs, snd s) \<Longrightarrow>
    (\<alpha> \<noteq> Tau \<longrightarrow> G (snd s) ss') \<and>
    (\<exists>sl'.
      sl' ## fs \<and>
      slf' = sl' + fs \<and>
      (\<alpha> = Tau \<longrightarrow> sl' = fst s) \<and>
      safe R F G I q n c' (sl', ss'))\<close>
  by (erule safe_sucE, (simp; fail))+


subsubsection \<open> Monotonicity of safe \<close>

lemma safe_monoD:
  \<open>safe R F G I q n c s \<Longrightarrow>
    R' \<le> R \<Longrightarrow>
    F' \<le> F \<Longrightarrow>
    G \<le> G' \<Longrightarrow>
    I \<le> I' \<Longrightarrow>
    q \<le> q' \<Longrightarrow>
    m \<le> n \<Longrightarrow>
    safe R' F' G' I' q' m c s\<close>
proof (induct arbitrary: m rule: safe.induct)
  case (safeI c s n)

  show ?case
  proof (rule safe.safeI)
    show \<open>c = Skip \<longrightarrow> q' s\<close>
      using safeI by auto
  next
    show \<open>I' s\<close>
      using safeI by auto
  next
    fix m' ss'
    assume assms2:
      \<open>m = Suc m'\<close>
      \<open>R' (snd s) ss'\<close>
    then obtain n' where
      \<open>n = Suc n'\<close>
      \<open>m' \<le> n'\<close>
      using safeI.prems Suc_leq_iff
      by blast
    then show
      \<open>safe R' F' G' I' q' m' c (fst s, ss')\<close>
      using safeI.prems assms2 safeI.hyps(4)
      by blast
  next
    fix m' fs \<alpha> lfs' ss' c'
    assume assms2:
      \<open>m = Suc m'\<close>
      \<open>((fst s + fs, snd s), c) \<midarrow>\<alpha>\<rightarrow> ((lfs', ss'), c')\<close>
      \<open>fst s ## fs\<close>
      \<open>F' (fs, snd s)\<close>
    then obtain n' where n_eqns:
      \<open>n = Suc n'\<close>
      \<open>m' \<le> n'\<close>
      using safeI.prems Suc_leq_iff
      by blast
    have fs_in_F: \<open>F (fs, snd s)\<close>
      by (meson assms2(4) predicate1D safeI.prems(2))
    then show
      \<open>(\<alpha> \<noteq> Tau \<longrightarrow> G' (snd s) ss') \<and>
        (\<exists>ls'.
          ls' ## fs \<and>
          lfs' = ls' + fs \<and>
          (\<alpha> = Tau \<longrightarrow> ls' = fst s) \<and>
          safe R' F' G' I' q' m' c' (ls', ss'))\<close>
      using safeI.hyps(5)[OF n_eqns(1) assms2(2-3) fs_in_F] safeI.prems n_eqns(2)
      by blast
  qed
qed

lemmas safe_mono = safe_monoD[rotated]

lemmas safe_mono_stepsD = safe_monoD[OF _ order.refl order.refl order.refl order.refl order.refl]
lemmas safe_mono_steps = safe_mono_stepsD[rotated]

lemmas safe_mono_invD = safe_monoD[OF _ order.refl order.refl order.refl _ order.refl order.refl]
lemmas safe_mono_inv = safe_mono_invD[rotated]

lemmas safe_mono_postD = safe_monoD[OF _ order.refl order.refl order.refl order.refl _ order.refl]
lemmas safe_mono_post = safe_mono_postD[rotated]

lemmas safe_mono_guarD = safe_monoD[OF _ order.refl order.refl _ order.refl order.refl order.refl]
lemmas safe_mono_guar = safe_mono_guarD[rotated]

lemmas safe_mono_frameD = safe_monoD[OF _ order.refl _ order.refl order.refl order.refl order.refl]
lemmas safe_mono_frame = safe_mono_frameD[rotated]


lemma safe_step_SucD:
  \<open>safe R F G I q (Suc n) c s \<Longrightarrow> safe R F G I q n c s\<close>
  by (metis safe_mono_stepsD le_add2 plus_1_eq_Suc)


section \<open> Soundness Helper Lemmas \<close>

subsection \<open> Safety of Skip \<close>

lemma safe_skip_iff:
  \<open>safe R F G I q n Skip s \<longleftrightarrow>
    (\<exists>sl ss. s = (sl, ss) \<and> (\<forall>k\<le>n. \<forall>ss'. (R^^k) ss ss' \<longrightarrow> q (sl, ss') \<and> I (sl, ss')))\<close>
  apply (induct n arbitrary: s)
   apply (simp; fail)
  apply (rule iffI)
   apply (erule safe_sucE)
   apply (clarsimp simp add: le_Suc_iff0)
   apply (metis relpowp_Suc_D2')
  apply (clarsimp simp add: safe_suc_iff le_Suc_iff0 all_conj_distrib imp_ex_conjL)
  apply (metis OO_def relpowp_commute)
  done

lemma safe_skip_stable_iff:
  assumes
    \<open>sswa R I \<le> I\<close>
    \<open>sswa R q \<le> q\<close>
  shows
    \<open>safe R F G I q n Skip s \<longleftrightarrow> q s \<and> I s\<close>
  using assms
  apply (simp add: safe_skip_iff sp_def le_fun_def imp_ex_conjL)
  apply (metis bot_nat_0.extremum relpowp_0_I rtranclp_power split_pairs2)
  done

lemma safe_skip':
  \<open>wssa R q s \<Longrightarrow> wssa R I s \<Longrightarrow> safe R F G I q n Skip s\<close>
  apply (induct n arbitrary: s)
   apply force
  apply (case_tac s)
  apply clarsimp
  apply (rule safeI)
     apply force
    apply force
   apply (simp add: wssa_step; fail)
  apply force
  done

lemma safe_skip:
  \<open>p s \<Longrightarrow> p \<le> wssa R q \<Longrightarrow> p \<le> wssa R I \<Longrightarrow> safe R F G I q n Skip s\<close>
  apply (rule safe_monoD[OF _ order.refl order.refl order.refl order.refl order.refl order.refl])
  apply (rule safe_skip'[where q=\<open>q\<close>])
   apply blast
  apply blast
  done


subsection \<open> Safety of frame \<close>

text \<open>
  The frame specification is 'lumpy', in that is represents the frames that could possibly
  come from other processes. These do \<^emph>\<open>not\<close> have to be downwards closed. The frame rule is,
  essentially, constructing a 'virtual' process.
    We must assume that the frame specification of the assumption includes not only the sepconj of
  the two elements, but also the frame spec. and frame predicate without any separating conjunction,
  i.e. \<open>F \<^emph>\<and> F' \<squnion> F'\<close>.
\<close>
lemma safe_frame':
  assumes ni_assms:
    \<open>sswa (R \<squnion> G) F' \<le> F'\<close>
  shows
    \<open>safe R (F \<^emph>\<and> F') G I q n c s \<Longrightarrow>
    fst s ## fs \<Longrightarrow>
    F' (fs, snd s) \<Longrightarrow>
    safe R F G (I \<^emph>\<and> F') (q \<^emph>\<and> F') n c (fst s + fs, snd s)\<close>
proof (induct arbitrary: fs rule: safe.induct)
  case (safeI c s n)

  note hyps = safeI.hyps[simplified safeI.prems(1)[simplified] fst_conv snd_conv]

  show ?case
    using safeI.prems(1-2) hyps(1-2)
    apply -
    apply (rule safe.safeI)
      (* subgoal: skip *)
       apply (force simp add: sepconj_conj_def simp del: sup_apply)
      (* subgoal: stateset *)
      apply (metis sepconj_conjI surjective_pairing)
      (* subgoal: rely step *)
     apply (simp del: sup_apply top_apply inf_apply)
     apply (rule hyps(4), fast, fast, fast)
     apply (cut_tac ni_assms(1))
     apply (meson predicate1D sswa_step sswa_trivial sup2I1; fail)
      (* subgoal: framed opstep *)
    apply (rename_tac n' fsx \<alpha> lfs' ss' c')
    apply (clarsimp simp add: partial_add_assoc2[of \<open>fst s\<close> fs] simp del: sup_apply top_apply)
    apply (frule hyps(5)[rotated 1])
       apply (metis disjoint_add_swap_lr)
      apply (simp add: sepconj_conj_apply)
      apply (metis disjoint_add_leftR disjoint_sym partial_add_commute)
     apply (simp add: disjoint_add_swap_lr; fail)
    apply (clarsimp simp del: top_apply sup_apply inf_apply)
    apply (erule opstep_act_cases)
     apply (simp add: disjoint_preservation2 partial_add_assoc2; fail)
    apply (rule_tac x=\<open>ls' + fs\<close> in exI)
    apply (intro conjI)
       apply (metis disjoint_add_leftR disjoint_add_swap_rl)
      apply (metis disjoint_add_leftR partial_add_assoc3)
     apply blast
    apply (drule_tac x=fs in spec, drule mp, rule disjoint_add_rightL[rotated], assumption)
     apply (metis disjoint_add_leftR)
    apply (drule mp[of \<open>F' _\<close>])
     apply (metis (full_types) ni_assms(1) predicate1D sswa_step sswa_trivial sup2I2)
    apply fast
    done
qed

lemma safe_frame:
  \<open>safe R (F \<^emph>\<and> F') G I q n c s \<Longrightarrow>
    fst s ## fs \<Longrightarrow>
    s' = (fst s + fs, snd s) \<Longrightarrow>
    sswa (R \<squnion> G) F' \<le> F' \<Longrightarrow>
    F' (fs, snd s) \<Longrightarrow>
    safe R F G (I \<^emph>\<and> F') (q \<^emph>\<and> F') n c s'\<close>
  by (simp add: safe_frame')


subsection \<open> Safety of Atomic \<close>

lemma safe_atom':
  \<open>\<forall>f\<le>F. sp ar (wssa R p \<^emph>\<and> f) \<le> sswa R q \<^emph>\<and> any_shared f \<Longrightarrow>
    wssa R p s \<Longrightarrow>
    safe R F
      (rel_image snd (pretest (sswa R p \<^emph>\<and> F) \<sqinter> ar)) \<comment> \<open> G \<close>
      (wssa R p \<squnion> sswa R q) \<comment> \<open> I \<close>
      (sswa R q) \<comment> \<open> q \<close>
      n \<langle>ar\<rangle> s\<close>
proof (induct n arbitrary: s)
  case (Suc n)
  note ih = Suc.hyps[simplified fst_conv snd_conv]
  show ?case
    using Suc.prems
    apply -
    apply (cases s)
    apply (rename_tac sl ss)
    apply (clarsimp simp del: sup_apply inf_apply top_apply predrel_apply rel_image_apply)
    apply (rule safeI)
      (* subgoal: termination *)
       apply force
      (* subgoal: state inv *)
      apply force
      (* subgoal: rely *)
     apply (clarsimp simp del: sup_apply inf_apply predrel_apply top_apply rel_image_apply)
     apply (simp add: ih wssa_step; fail)
      (* subgoal: local framed opstep *)
    apply (rule conjI)
      (* subsubgoal: guarantee *)
     apply clarsimp
     apply (meson rely_rel_wlp_impl_sp sepconj_conjI; fail)
      (* subsubgoal: safety after opstep *)
    apply (clarsimp simp del: sup_apply inf_apply top_apply predrel_apply
        simp add: safe_skip_stable_iff sp_sup)
    apply (frule spec[of _ \<open>(=) _\<close>], frule mp, blast)
    apply (clarsimp simp add: sp_def[of ar] le_fun_def imp_ex_conjL sepconj_conj_def any_shared_def)
    done
qed simp

lemma safe_atom:
  \<open>\<forall>f\<le>F. sp ar (sswa R p \<^emph>\<and> f) \<le> q \<^emph>\<and> any_shared f \<Longrightarrow>
    rel_image snd (pretest (sswa R p \<^emph>\<and> F) \<sqinter> ar) \<le> G \<Longrightarrow>
    wssa R p s \<Longrightarrow>
    sswa R p \<le> I \<Longrightarrow>
    sswa R q \<le> I \<Longrightarrow>
    sswa R q \<le> q' \<Longrightarrow>
    safe R F G I q' n \<langle>ar\<rangle> s\<close>
  apply (rule safe_monoD[OF safe_atom'[where p=\<open>sswa R p\<close> and q=q] order.refl order.refl _ _ _ order.refl])
      apply simp
      apply (meson order_trans sepconj_conj_monoL sswa_weaker; fail)
     apply auto
  done


subsection \<open> Safety of Sequencing \<close>

lemma safe_seq_assoc_left:
  \<open>safe R F G I q n c s \<Longrightarrow>
    c = (c1 ;; c2 ;; c3) \<Longrightarrow>
    safe R F G I q n ((c1 ;; c2) ;; c3) s\<close>
  apply (induct arbitrary: c1 c2 c3 rule: safe.inducts)
  apply (rule safeI)
     apply blast
    apply blast
   apply blast
  apply (simp, elim disjE conjE exE)
   apply force
  apply metis
  done

lemma safe_seq_assoc_right:
  \<open>safe R F G I q n c s \<Longrightarrow>
    c = ((c1 ;; c2) ;; c3) \<Longrightarrow>
    safe R F G I q n (c1 ;; c2 ;; c3) s\<close>
  apply (induct arbitrary: c1 c2 c3 rule: safe.inducts)
  apply (rule safeI)
     apply blast
    apply blast
   apply blast
  apply (simp, elim disjE conjE exE)
   apply force
  apply metis
  done

lemma safe_seq':
  \<open>safe R F Ga Ia q n ca s \<Longrightarrow>
    \<forall>s'. q s' \<longrightarrow> safe R F Gb Ib q' n cb s' \<Longrightarrow>
    safe R F (Ga \<squnion> Gb) (Ia \<squnion> Ib) q' n (ca ;; cb) s\<close>
proof (induct arbitrary: cb q' rule: safe.inducts)
  case (safeI c s n)
  show ?case
    using safeI.hyps(1-2)
    apply -
    apply (rule safe.safeI)
      (* subgoal: skip *)
       apply fast
      (* subgoal: stateset *)
      apply fast
      (* subgoal: rely *)
     apply (metis safeI.hyps(4) safeI.prems safe_step_SucD)
      (* subgoal: local framed opstep *)
    apply (clarsimp simp del: sup_apply)
    apply (elim disjE conjE exE)
     apply (metis safeI.prems safe_mono_guarD safe_mono_invD safe_step_SucD act.distinct(1)
        sup.cobounded2 surjective_pairing)
    apply (frule(3) safeI.hyps(5))
    apply (clarsimp simp del: sup_apply)
    apply (metis safeI.prems safe_step_SucD sup2I1)
    done
qed

lemma safe_seq:
  \<open>safe R F Ga Ia q n ca s \<Longrightarrow>
    \<forall>s'. q s' \<longrightarrow> safe R F Gb Ib q' n cb s' \<Longrightarrow>
    Ga \<le> G \<Longrightarrow>
    Gb \<le> G \<Longrightarrow>
    Ia \<le> I \<Longrightarrow>
    Ib \<le> I \<Longrightarrow>
    safe R F G I q' n (ca ;; cb) s\<close>
  by (rule safe_monoD[OF safe_seq' order.refl order.refl _ _ order.refl order.refl])
    blast+


subsection \<open> Safety of Iter \<close>

lemma safe_iter':
  \<open>\<forall>s'. wssa R i s' \<longrightarrow> safe R F G I (wssa R i) n c s' \<Longrightarrow>
    wssa R i s \<Longrightarrow>
    safe R F G I (wssa R i) n (Iter c) s\<close>
proof (induct n arbitrary: i s)
  case (Suc n)
  have safe_n_c:
    \<open>\<forall>s'. wssa R i s' \<longrightarrow> safe R F G I (wssa R i) n c s'\<close>
    using Suc.prems(1) by (meson safe_step_SucD)
  note safe_ih = Suc.hyps[OF safe_n_c]

  have safe_suc_c:
    \<open>\<And>s'. wssa R i s' \<Longrightarrow> safe R F G I (wssa R i) (Suc n) c s'\<close>
    using Suc.prems(1) by blast
  note safe_suc_cD = safe_sucD[OF safe_suc_c]

  show ?case
    using Suc.prems(1-2)
    apply -
    apply (rule safe.safeI)
      (* subgoal: skip *)
       apply blast
      (* subgoal: stateset *)
      apply blast
      (* subgoal: rely *)
     apply (metis Suc_inject surjective_pairing safe_ih wssa_step)
      (* subgoal: framed opstep *)
    apply (simp add: le_fun_def del: split_paired_All)
    apply (elim disjE conjE exE)
     apply (clarsimp simp add: safe_skip_iff)
     apply (metis (no_types) relpowp_imp_rtranclp rtranclp_idemp safe_sucE split_pairs wssa_step)
    apply (rule conjI, fast)
    apply (frule(3) safe_suc_cD(2))
    apply clarsimp
    apply (rule_tac x=sl' in exI)
    apply (intro conjI)
       apply blast
      apply blast
     apply blast
    apply (rule safe_seq[OF _ allI[OF impI[OF safe_ih]]]; blast)
    done
qed force

lemma safe_iter:
  \<open>\<forall>s'. wssa R i s' \<longrightarrow> safe R F G I (wssa R i) n c s' \<Longrightarrow>
    wssa R i s \<Longrightarrow>
    wssa R i \<le> q' \<Longrightarrow>
    safe R F G I q' n (Iter c) s\<close>
  using safe_iter'
  by (metis (no_types, opaque_lifting) safe_mono_postD)


subsubsection \<open> Safety of internal nondeterminism \<close>

lemma safe_indet':
  \<open>safe R F Ga Ia qa n ca s \<Longrightarrow>
      safe R F Gb Ib qb n cb s \<Longrightarrow>
      safe R F (Ga \<squnion> Gb) (Ia \<squnion> Ib) (qa \<squnion> qb) n (ca \<^bold>\<sqinter> cb) s\<close>
proof (induct n arbitrary: ca cb s)
  case (Suc n)
  show ?case
    using Suc.prems
    apply -
    apply (rule safeI)
      (* subgoal: rely *)
       apply blast
      (* subgoal: state inv *)
      apply blast
      (* subgoal: rely *)
     apply (metis Suc.hyps nat.inject safe_sucD(1))
      (* subgoal: framed opstep *)
    apply (clarsimp simp add: conj_disj_distribL[symmetric] simp del: sup_apply)
    apply (meson Suc_n_not_le_n order.refl inf_sup_ord(3,4) linorder_le_cases safe_mono; fail)
    done
qed blast

lemma safe_indet:
  \<open>safe R F Ga Ia qa n ca s \<Longrightarrow>
      safe R F Gb Ib qb n cb s \<Longrightarrow>
      Ia \<le> I \<Longrightarrow>
      Ib \<le> I \<Longrightarrow>
      Ga \<le> G \<Longrightarrow>
      Gb \<le> G \<Longrightarrow>
      qa \<le> q \<Longrightarrow>
      qb \<le> q \<Longrightarrow>
      safe R F G I q n (ca \<^bold>\<sqinter> cb) s\<close>
  by (rule safe_monoD[OF safe_indet' order.refl order.refl _ _ _ order.refl])
    blast+


subsubsection \<open> Safety of external nondeterminism \<close>

lemma safe_endet':
  \<open>safe R F Ga Ia qa n ca s \<Longrightarrow>
    safe R F Gb Ib qb n cb s \<Longrightarrow>
    safe R F (Ga \<squnion> Gb) (Ia \<squnion> Ib) (qa \<squnion> qb) n (ca \<^bold>\<box> cb) s\<close>
proof (induct n arbitrary: ca cb s)
  case (Suc n)
  show ?case
    using Suc.prems
    apply -
    apply (rule safeI)
      (* subgoal: skip *)
       apply blast
      (* subgoal: state inv. *)
      apply blast
      (* subgoal: rely *)
     apply (metis Suc.hyps nat.inject safe_sucD(1))
      (* subgoal: local frame opstep *)
    apply (clarsimp simp del: sup_apply)
    apply (rule conjI)
     apply (metis act.distinct(1) safe_sucE sup2I1 sup2I2)
    apply (simp only: disj.assoc[symmetric, of _ _ \<open>_ \<or> _\<close>])
    apply (erule disjE, erule disjE)
      apply (clarsimp simp add: conj_disj_distribR_middle[symmetric] conj_disj_distribL[symmetric])
      apply (meson inf_sup_ord(4) lessI order_le_less safe_mono sup.cobounded1; fail)
     apply (elim disjE; clarify)
      apply (frule(3) safe_sucD(2))
      apply (metis Suc.hyps opstep_tau_preserves_state split_pairs2 safe_step_SucD)
     apply (frule(3) safe_sucD(2))
     apply (metis Suc.hyps opstep_tau_preserves_state split_pairs2 safe_step_SucD)
    apply (elim disjE; clarify)
     apply (frule(3) safe_sucD(2))
     apply clarsimp
     apply (intro exI conjI, assumption, rule refl)
     apply (meson safe_mono order.refl sup_ge1; fail)
    apply (frule(3) safe_sucD(2))
    apply clarsimp
    apply (intro exI conjI, assumption, rule refl)
    apply (meson safe_mono order.refl sup_ge2; fail)
    done
qed blast

lemma safe_endet:
  \<open>safe R F Ga Ia qa n ca s \<Longrightarrow>
    safe R F Gb Ib qb n cb s \<Longrightarrow>
    Ia \<le> I \<Longrightarrow>
    Ib \<le> I \<Longrightarrow>
    Ga \<le> G \<Longrightarrow>
    Gb \<le> G \<Longrightarrow>
    qa \<le> q \<Longrightarrow>
    qb \<le> q \<Longrightarrow>
    safe R F G I q n (ca \<^bold>\<box> cb) s\<close>
  by (rule safe_monoD[OF safe_endet' order.refl order.refl _ _ _ order.refl])
    blast+


subsection \<open> Safety of parallel \<close>

lemma safe_parallel':
  \<open>safe (R \<squnion> Gb) (Ib \<^emph>\<and> F) Ga Ia qa n ca (sla, ss) \<Longrightarrow>
    safe (R \<squnion> Ga) (Ia \<^emph>\<and> F) Gb Ib qb n cb (slb, ss) \<Longrightarrow>
    sla ## slb \<Longrightarrow>
    safe R F (Ga \<squnion> Gb)
      (sswa (R \<squnion> Gb) Ia \<^emph>\<and> sswa (R \<squnion> Ga) Ib)
      (sswa (R \<squnion> Gb) qa \<^emph>\<and> sswa (R \<squnion> Ga) qb)
      n (ca \<parallel> cb) (sla + slb, ss)\<close>
proof (induct n arbitrary: ca cb sla slb ss)
  case (Suc n)

  note safe_suc1 = safe_sucD[OF Suc.prems(1), simplified fst_conv snd_conv]
  note safe_suc2 = safe_sucD[OF Suc.prems(2), simplified fst_conv snd_conv]

  show ?case
  proof (rule safeI; fast?; (intro conjI)?; (simp only: fst_conv snd_conv)?)
    show \<open>(sswa (R \<squnion> Gb) Ia \<^emph>\<and> sswa (R \<squnion> Ga) Ib) (sla + slb, ss)\<close>
      using Suc.prems(3) safe_suc1(2) safe_suc2(2)
      by (simp del: sup_apply,
          metis Suc.prems(1,2) safe_then_state_inv sepconj_conjI sswa_trivial)
  next
    fix m ss'
    assume r_step: \<open>R ss ss'\<close>
    presume m_eq_n: \<open>Suc m = Suc n\<close>

    show
      \<open>safe R F (Ga \<squnion> Gb)
        (sswa (R \<squnion> Gb) Ia \<^emph>\<and> sswa (R \<squnion> Ga) Ib)
        (sswa (R \<squnion> Gb) qa \<^emph>\<and> sswa (R \<squnion> Ga) qb)
        m (ca \<parallel> cb) (sla + slb, ss')\<close>
      using r_step m_eq_n Suc.prems(1-3)
      apply (simp del: sup_apply)
      apply (intro Suc.hyps)
        apply fastforce
       apply (fastforce dest: safe_step_SucD[where c=ca and n=n])
      apply fast
      done
  next
    fix m \<alpha> c' sf slf' ss'
    assume assms2:
      \<open>sla + slb ## sf\<close>
      \<open>opstep \<alpha> ((sla + slb + sf, ss), ca \<parallel> cb) ((slf', ss'), c')\<close>
      \<open>F (sf, ss)\<close>

    presume m_eq_n:
      \<open>Suc m = Suc n\<close>

    have disjoint_parts:
      \<open>sla ## sf\<close>
      \<open>slb ## sf\<close>
      using Suc.prems(3) assms2(1)
      by (force dest: disjoint_add_leftL disjoint_add_leftR)+

    have framed_invs:
      \<open>(Ia \<^emph>\<and> F) (sla + sf, ss)\<close>
      \<open>(Ib \<^emph>\<and> F) (slb + sf, ss)\<close>
      using Suc.prems(1-2) assms2(1,3)
      by (metis disjoint_parts(1-2) safe_then_state_inv sepconj_conjI sup1CI)+

    show \<open>\<alpha> \<noteq> Tau \<longrightarrow> (Ga \<squnion> Gb) ss ss'\<close>
      using Suc.prems(2,3) assms2 disjoint_parts framed_invs safe_suc1(1,2)
      by (clarsimp simp del: sup_apply)
        (metis act.simps(2) disjoint_add_left_commute disjoint_add_left_commute2 disjoint_add_swap_lr2
          partial_add_assoc3 partial_add_left_commute safe_suc2(2))

    show \<open>\<exists>sl'.
            sl' ## sf \<and>
            slf' = sl' + sf \<and>
            (\<alpha> = Tau \<longrightarrow> sl' = sla + slb) \<and>
            safe R F (Ga \<squnion> Gb)
              (sswa (R \<squnion> Gb) Ia \<^emph>\<and> sswa (R \<squnion> Ga) Ib)
              (sswa (R \<squnion> Gb) qa \<^emph>\<and> sswa (R \<squnion> Ga) qb)
              m c' (sl', ss')\<close>
      using assms2 m_eq_n Suc.prems(3) safe_suc1(1) safe_suc2(1) framed_invs
      apply (simp add: del: sup_apply)
      apply (elim disjE conjE exE)
        (* subgoal: done *)
        apply (clarsimp simp del: sup_apply simp add: safe_skip_stable_iff
          sp_rely_sepconj_conj_semidistrib_mono)
        apply (metis Suc.prems(1,2) safe_then_postcond safe_then_state_inv sepconj_conjI sswa_trivial)
        (* subgoal: left *)
       apply (simp add: partial_add_assoc2[of sla slb] del: sup_apply)
       apply (frule safe_suc1(2))
         apply (metis disjoint_add_swap_lr)
        apply blast
       apply (clarsimp simp del: sup_apply)
       apply (rule_tac x=\<open>sl' + slb\<close> in exI)
       apply (intro conjI)
          apply (metis disjoint_add_leftR disjoint_add_swap_rl)
         apply (metis disjoint_add_leftR partial_add_assoc3)
        apply blast
       apply (rule Suc.hyps)
         apply blast
        apply (erule opstep_act_cases)
         apply (cut_tac safe_step_SucD[OF Suc.prems(2)], force)
        apply blast
       apply (metis disjoint_add_rightL disjoint_parts(2))
        (* subgoal right *)
      apply (simp add: partial_add_commute[of sla] partial_add_assoc2[of slb]
          disjoint_sym_iff del: sup_apply)
      apply (frule safe_suc2(2))
        apply (metis disjoint_add_right_commute2 partial_add_commute)
       apply fast
      apply (clarsimp simp del: sup_apply)
      apply (rule_tac x=\<open>sla + sl'\<close> in exI)
      apply (intro conjI)
         apply (metis disjoint_parts(1) disjoint_add_right_commute2 disjoint_sym)
        apply (metis disjoint_parts(1) disjoint_add_rightL partial_add_assoc3 partial_add_commute)
       apply (blast dest: partial_add_commute)
      apply (rule Suc.hyps)
        apply (erule opstep_act_cases)
         apply (cut_tac safe_step_SucD[OF Suc.prems(1)], force)
        apply blast
       apply blast
      apply (metis disjoint_add_rightL disjoint_parts(1) disjoint_sym)
      done
  qed simp+
qed (blast intro: sepconj_conjI)

lemma safe_parallel:
  \<open>safe (R \<squnion> Gb) (Ib \<^emph>\<and> F) Ga Ia qa n ca (sla, ss) \<Longrightarrow>
    safe (R \<squnion> Ga) (Ia \<^emph>\<and> F) Gb Ib qb n cb (slb, ss) \<Longrightarrow>
    sla ## slb \<Longrightarrow>
    sswa (R \<squnion> Gb) qa \<^emph>\<and> sswa (R \<squnion> Ga) qb \<le> q \<Longrightarrow>
    sswa (R \<squnion> Gb) Ia \<^emph>\<and> sswa (R \<squnion> Ga) Ib \<le> I \<Longrightarrow>
    Ga \<squnion> Gb \<le> G \<Longrightarrow>
    safe R F G I q n (ca \<parallel> cb) (sla + slb, ss)\<close>
  using safe_parallel' safe_mono[OF order.refl order.refl _ _ _ order.refl]
  by meson


subsection \<open> Safety of conj \<close>

lemma safe_conj:
  \<open>safe R F Ga Ia qa n c s \<Longrightarrow>
    cancellative' Ia Ib (sswa (Ga \<sqinter> Gb) F) \<Longrightarrow>
    safe R F Gb Ib qb n c s \<Longrightarrow>
    safe R F (Ga \<sqinter> Gb) (Ia \<sqinter> Ib) (qa \<sqinter> qb) n c s\<close>
proof (induct rule: safe.induct)
  case (safeI c s n)
  show ?case
    using safeI.prems
    apply -
    apply (rule safe.safeI)
       apply (cut_tac safeI.hyps(1))
       apply (blast dest: safe_then_postcond)
      apply (cut_tac safeI.hyps(2))
      apply (blast dest: safe_then_state_inv)
      (* subgoal: rely *)
     apply (metis safeI.hyps(4) safe_sucD(1))
      (* subgoal: framed opstep *)
    apply (clarsimp simp del: inf_apply sup_apply)
    apply (frule(3) safe_sucD(2)[where q=qb])
    apply (frule(3) safeI.hyps(5))
    apply (rule conjI, blast)
    apply (clarsimp simp del: inf_apply sup_apply)
    apply (subgoal_tac \<open>(\<alpha> = Vis \<longrightarrow> Ga (snd s) ss' \<and> Gb (snd s) ss') \<and> (\<alpha> = Tau \<longrightarrow> ss' = snd s)\<close>)
     prefer 2
     apply (metis (no_types) opstep_tau_preserves_state fst_conv snd_conv)
    apply (rename_tac la' lb')
    apply (subgoal_tac \<open>sswa (Ga \<sqinter> Gb) F (fs, ss')\<close>)
     prefer 2
     apply (metis (full_types) act.exhaust inf2I sswa_stepD sswa_trivial)
    apply (subgoal_tac \<open>la' = lb'\<close>)
     prefer 2
     apply (frule_tac s=\<open>(la', ss')\<close> in safe_then_state_inv)
     apply (frule_tac s=\<open>(lb', ss')\<close> in safe_then_state_inv)
     apply (simp add: cancellative'_def del: inf_apply sup_apply)
     apply metis
    apply metis
    done
qed

lemma safe_Conj':
  assumes niassms:
    \<open>cancellative' (\<Squnion>\<I>) (\<Squnion>\<I>) (sswa (\<Squnion>\<G>) F)\<close>
    \<open>\<G> \<noteq> {}\<close>
    \<open>\<I> \<noteq> {}\<close>
    \<open>Q \<noteq> {}\<close>
    and iassms:
    \<open>\<forall>G\<in>\<G>. \<forall>I\<in>\<I>. \<forall>q\<in>Q. safe R F G I q n c s\<close>
  shows
    \<open>safe R F (\<Sqinter>\<G>) (\<Sqinter>\<I>) (\<Sqinter>Q) n c s\<close>
  using iassms
proof (induct n arbitrary: c s)
  case 0
  then show ?case
    using niassms(2-)
    by (force simp add: ball_conj_distrib)
next
  case (Suc n)
  show ?case
    using Suc.prems niassms
    apply -
    apply (rule safeI)
      (* termination *)
       apply (metis Suc.hyps Inf1_I safe_then_postcond)
      (* invariant *)
      apply (metis Suc.hyps Inf1_I safe_then_state_inv)
      (* rely step *)
     apply (clarsimp simp del: Inf_apply)
     apply (rule Suc.hyps; blast)
      (* framed opstep *)
    apply (clarsimp simp del: inf_apply Inf_apply)
    apply (subgoal_tac \<open>(\<exists>G. G \<in> \<G>) \<and> (\<exists>I. I \<in> \<I>) \<and> (\<exists>q. q \<in> Q)\<close>)
     prefer 2
     apply blast
    apply (clarsimp simp del: inf_apply)
    apply (rename_tac Ga Ia qa)
    apply (frule bspec[of \<G>], assumption, drule bspec[of \<I>], assumption, drule bspec[of Q], assumption)
    apply (frule(3) safe_sucD(2))
    apply (clarsimp simp del: inf_apply)
    apply (rule conjI)
      (** guar *)
     apply (metis safe_sucE)
    apply (rule_tac x=sl' in exI)
    apply (intro conjI)
       apply blast
      apply blast
     apply blast
    apply (rule Suc.hyps)
    apply (clarsimp simp del: inf_apply)
    apply (rename_tac Gb Ib qb)
    apply (drule_tac x=Gb in bspec, assumption, drule_tac x=Ib in bspec, assumption,
        drule_tac x=qb in bspec, assumption)
    apply (frule(3) safe_sucD(2))
    apply (clarsimp simp del: inf_apply)
    apply (subgoal_tac \<open>sswa (\<Squnion>\<G>) F (fs, ss')\<close>)
     prefer 2
     apply (erule opstep_act_cases)
      apply force
     apply (clarsimp simp del: inf_apply)
     apply (rule sswa_step)
      apply (rule_tac r=Ga in Sup2_I)
       apply blast
      apply blast
     apply blast
    apply (simp add: cancellative'_def Bex_def imp_ex_conjL)
    apply (metis safe_then_state_inv)
    done
qed


subsection \<open> Safe Soundness \<close>

lemma soundness_safe:
  assumes \<open>rgsat c R G p q I F T\<close>
    and \<open>p s\<close>
  shows \<open>safe R F G I q n c s\<close>
  using assms
proof (induct c R G p q I F T arbitrary: n s rule: rgsat.inducts)
  case (rgsat_skip R p q I T F G)
  then show ?case
    by (intro safe_skip[where p=p]; simp add: wlp_weaker_iff_sp_stronger)
next
  case (rgsat_iter c R G i I F T p q I')
  then show ?case
    apply (intro safe_iter[where i=\<open>sswa R i\<close> and R=R, simplified])
      apply (meson order.refl safe_monoD sswa_weaker; fail)
     apply blast
    apply blast
    done
next
  case (rgsat_seq ca r g p pp Ia F T cb q Ib I)
  then show ?case
    by (intro safe_seq) blast+
next
  case (rgsat_indet ca r ga p qa Ia F T cb gb qb Ib g q I)
  then show ?case
    by (intro safe_indet) fast+
next
  case (rgsat_endet c1 r Ga p qa Ia F T c2 Gb qb Ib g q I)
  then show ?case
    by (intro safe_endet) fast+
next
  case (rgsat_par ca R Gb Ga pa qa Ia Ib F T cb pb qb G p q I)
  moreover obtain sla slb ss where
    \<open>pa (sla, ss)\<close>
    \<open>pb (slb, ss)\<close>
    \<open>sla ## slb\<close>
    \<open>s = (sla + slb, ss)\<close>
    using rgsat_par.hyps(7) rgsat_par.prems(1)
    by (simp add: split_pairs le_fun_def sepconj_conj_apply, metis surjective_pairing)
  ultimately show ?case
    by (simp del: sup_apply top_apply,
        intro safe_parallel[where Ga=Ga and Gb=Gb and Ia=Ia and Ib=Ib and qa=qa and qb=qb];
        simp del: sup_apply top_apply)
next
  case (rgsat_atom p' R p q q' ar G F I C)
  then show ?case
    by (intro safe_atom[where p=\<open>wssa R p\<close> and q=q])
      (simp add: le_fun_def del: split_paired_All; fail)+
next
  case (rgsat_frame c R G p q I F F' C)
  then show ?case
    apply -
    apply (clarsimp simp add: sepconj_conj_apply2[where s=s] simp del: top_apply sup_apply)
    apply (rule_tac safe_frame, assumption)
       apply (simp add: split_pairs2; fail)+
    done
next
  case (rgsat_weaken c R' G' p' q' I' F' T p q R G I F)
  moreover have \<open>p' s\<close>
    using rgsat_weaken.hyps(3) rgsat_weaken.prems
    by blast
  moreover then have \<open>safe R' F' G' I' q' n c s\<close>
    using rgsat_weaken.prems rgsat_weaken.hyps(2)
    by fast
  ultimately show ?case
    by (meson order.refl safe_monoD)
next
  case rgsat_Disj
  then show ?case by fast
next
  case (rgsat_Conj \<I> I' \<G> G' Q q' c R p F C)
  have Aa: \<open>\<forall>n. \<forall>G\<in>\<G>. \<forall>I\<in>\<I>. \<forall>q\<in>Q. safe R F G I q n c s\<close>
    using rgsat_Conj.hyps(7) rgsat_Conj.prems
    by blast
  then show ?case
    using rgsat_Conj.prems safe_Conj'[OF rgsat_Conj(8) rgsat_Conj(5,4,6)]
      rgsat_Conj.hyps(1-3)
    by (meson safe_mono_guarD safe_mono_invD safe_mono_postD)
qed


section \<open> Semantic Proof \<close>

definition semsat (\<open>_, _, _, _ \<Turnstile> { _ } _ { _ }\<close> [50,0,0,0,0,50,0] 50) where
  \<open>R, G, F, I \<Turnstile> { p } c { q } \<equiv> \<forall>n. p \<le> safe R F G I q n c\<close>

lemma semsat_weaken:
  \<open>R, G, F, I \<Turnstile> { p } c { q } \<Longrightarrow>
    R' \<le> R \<Longrightarrow>
    G \<le> G' \<Longrightarrow>
    F' \<le> F \<Longrightarrow>
    I \<le> I' \<Longrightarrow>
    p' \<le> p \<Longrightarrow>
    q \<le> q' \<Longrightarrow>
    R', G', F', I' \<Turnstile> { p' } c { q' }\<close>
  unfolding semsat_def
  apply clarsimp
  apply (rule safe_mono[OF _ _ _ _ _ order.refl]; assumption?)
  apply blast
  done

lemmas semsat_weaken_guar_inv =
  semsat_weaken[OF _ order.refl _ order.refl _ order.refl order.refl]

lemmas semsat_weaken_guar_inv_post =
  semsat_weaken[OF _ order.refl _ order.refl _ order.refl _]

lemmas semsat_weaken_prepost =
  semsat_weaken[OF _ order.refl order.refl order.refl order.refl]

lemma semsat_skip:
  \<open>p \<le> wssa R px \<Longrightarrow>
    sswa R px \<le> q \<Longrightarrow>
    sswa R p \<le> I \<Longrightarrow>
    R, G, F, I \<Turnstile> { p } Skip { q }\<close>
  unfolding semsat_def
  apply clarsimp
  apply (rule safe_skip[of p])
    apply blast
   apply (meson order.trans wlp_weaker_iff_sp_stronger wssa_stronger; fail)
  apply (meson order.trans wlp_weaker_iff_sp_stronger wssa_stronger; fail)
  done

lemma semsat_frame:
  \<open>R, G, F \<^emph>\<and> F', I \<Turnstile> { p } c { q } \<Longrightarrow>
    sswa (R \<squnion> G) F' \<le> F' \<Longrightarrow>
    R, G, F, I \<^emph>\<and> F' \<Turnstile> { p \<^emph>\<and> F' } c { q \<^emph>\<and> F' }\<close>
  unfolding semsat_def
  using safe_frame
  by (fastforce simp add: sepconj_conj_apply)

lemma semsat_atom:
  \<open>\<forall>f\<le>F. sp ar (p \<^emph>\<and> f) \<le> q \<^emph>\<and> any_shared f \<Longrightarrow>
    rel_image snd (pretest (p \<^emph>\<and> F) \<sqinter> ar) \<le> G \<Longrightarrow>
    sswa R p \<le> I \<Longrightarrow>
    sswa R q \<le> I \<Longrightarrow>
    R, G, F, I \<Turnstile> { wssa R p } \<langle>ar\<rangle> { sswa R q }\<close>
  unfolding semsat_def
  apply clarsimp
  apply (rule safe_atom[where p=\<open>wssa R p\<close> and q=q])
       apply (simp, meson order.trans sepconj_conj_monoL sp_pred_mono wssa_stronger; fail)
      apply (clarsimp simp add: le_fun_def imp_ex_conjL all_conj_distrib)
      apply (metis sepconj_conj_def wssa_trivial)
     apply fastforce
    apply fastforce
   apply blast
  apply blast
  done

lemma semsat_seq:
  \<open>R, G, F, I \<Turnstile> { p } ca { px } \<Longrightarrow>
    R, G, F, I \<Turnstile> { px } cb { q } \<Longrightarrow>
    R, G, F, I \<Turnstile> { p } (ca ;; cb) { q }\<close>
  apply (clarsimp simp add: semsat_def le_fun_def)
  apply (rule safe_seq, fast+)
  done

lemma semsat_iter:
  \<open>R, G, F, I \<Turnstile> { sswa R i } c { i } \<Longrightarrow>
    R, G, F, I \<Turnstile> { i } Iter c { sswa R i }\<close>
  unfolding semsat_def
  apply (clarsimp simp add: le_fun_def)
  apply (rule safe_iter[where i=\<open>sswa R i\<close>])
    apply (simp, meson safe_mono_postD sswa_weaker; fail)
   apply force
  apply force
  done

lemma semsat_indet:
  \<open>R, G, F, I \<Turnstile> { p } ca { qa } \<Longrightarrow>
    R, G, F, I \<Turnstile> { p } cb { qb } \<Longrightarrow>
    R, G, F, I \<Turnstile> { p } ca \<^bold>\<sqinter> cb { qa \<squnion> qb }\<close>
  unfolding semsat_def
  by (clarsimp simp add: le_fun_def)
    (rule safe_indet[where Ga=G and Gb=G and Ia=I and Ib=I and qa=qa and qb=qb]; blast)

lemma semsat_endet:
  \<open>R, G, F, I \<Turnstile> { p } ca { qa } \<Longrightarrow>
    R, G, F, I \<Turnstile> { p } cb { qb } \<Longrightarrow>
    R, G, F, I \<Turnstile> { p } ca \<^bold>\<box> cb { qa \<squnion> qb }\<close>
  unfolding semsat_def
  by (clarsimp simp add: le_fun_def)
    (rule safe_endet[where Ga=G and Gb=G and Ia=I and Ib=I and qa=qa and qb=qb]; blast)

lemma semsat_par:
  \<open>R \<squnion> Gb, Ga, Ib \<^emph>\<and> F, Ia \<Turnstile> { pa } ca { qa } \<Longrightarrow>
    R \<squnion> Ga, Gb, Ia \<^emph>\<and> F, Ib \<Turnstile> { pb } cb { qb } \<Longrightarrow>
    R, Ga \<squnion> Gb, F, (sswa (R \<squnion> Gb) Ia \<^emph>\<and> sswa (R \<squnion> Ga) Ib) \<Turnstile>
      { pa \<^emph>\<and> pb }
      ca \<parallel> cb
      { sswa (R \<squnion> Gb) qa \<^emph>\<and> sswa (R \<squnion> Ga) qb }\<close>
  unfolding semsat_def
  apply (clarsimp simp add: le_fun_def sepconj_conj_apply)
  apply (rule safe_parallel[of R Gb Ib F Ga Ia qa _ ca _ _ qb cb, OF _ _ _ order.refl order.refl order.refl])
    apply blast+
  done

lemma semsat_Conj:
  assumes niassms:
    \<open>cancellative' (\<Squnion>\<I>) (\<Squnion>\<I>) (sswa (\<Squnion>\<G>) F)\<close>
    \<open>\<G> \<noteq> {}\<close>
    \<open>\<I> \<noteq> {}\<close>
    \<open>Q \<noteq> {}\<close>
    and iassms:
    \<open>\<forall>G\<in>\<G>. \<forall>I\<in>\<I>. \<forall>q\<in>Q. R, G, F, I \<Turnstile> { p } c { q }\<close>
  shows
    \<open>R, \<Sqinter>\<G>, F, \<Sqinter>\<I> \<Turnstile> { p } c { \<Sqinter>Q }\<close>
  using assms
  unfolding semsat_def
  apply clarsimp
  apply (rule safe_Conj', blast+)
  done

lemma semsat_Disj:
  assumes \<open>\<forall>p\<in>P. R, G, F, I \<Turnstile> { p } c { q }\<close>
  shows \<open>R, G, F, I \<Turnstile> { \<Squnion>P } c { q }\<close>
  using assms
  unfolding semsat_def
  by force

lemma soundness:
  assumes \<open>R, G, I, F, T \<turnstile> { p } c { q }\<close>
  shows \<open>R, G, F, I \<Turnstile> { p } c { q }\<close>
  using assms
proof (induct rule: rgsat.inducts)
  case (rgsat_skip R p q I T G F)
  then show ?case
    by (intro semsat_skip[where px=\<open>sswa R p\<close>])
      force+
next
  case (rgsat_iter c R G i I F T p q)
  then show ?case
    by (meson semsat_iter semsat_weaken sswa_weaker order.refl)
next
  case (rgsat_seq ca R G p pp Ia F T cb q Ib I)
  then show ?case
    by (meson semsat_seq semsat_weaken order.refl)
next
  case (rgsat_indet ca R Ga p qa Ia F T cb Gb qb Ib G q I)
  then show ?case
    using semsat_indet[
        OF semsat_weaken_guar_inv[OF _ sup.cobounded1 sup.cobounded1]
        semsat_weaken_guar_inv[OF _ sup.cobounded2 sup.cobounded2],
        THEN semsat_weaken_guar_inv_post[OF _ sup_least sup_least sup_least]]
    by fastforce
next
  case (rgsat_endet ca R Ga p qa Ia F T cb Gb qb Ib G q I)
  then show ?case
    using semsat_endet[
        OF semsat_weaken_guar_inv[OF _ sup.cobounded1 sup.cobounded1]
        semsat_weaken_guar_inv[OF _ sup.cobounded2 sup.cobounded2],
        THEN semsat_weaken_guar_inv_post[OF _ sup_least sup_least sup_least]]
    by fastforce
next
  case (rgsat_par ca R Gb Ga pa qa Ia Ib F T cb pb qb G p q I)
  then show ?case
    by (meson semsat_par semsat_weaken sup.bounded_iff order.refl)
next
  case (rgsat_atom p' R p q q' ar F G I T)
  then show ?case
    by (intro semsat_weaken_prepost[OF semsat_atom]) (simp; fail)+
next
  case (rgsat_frame c R G p q I F F' T)
  then show ?case
    by (meson semsat_frame)
next
  case (rgsat_weaken c r' g' p' q' I' F' T p q r g I F)
  then show ?case
    by (meson semsat_weaken)
next
  case (rgsat_Disj p' P c R G q I F T)
  then show ?case
    by (meson order_trans semsat_Disj semsat_def)
next
  case (rgsat_Conj \<I> I' \<G> G' Q q' c R p F T)
  then show ?case
    by (meson semsat_Conj semsat_weaken_guar_inv_post)
qed


end