theory Semantics
  imports RGLogic
begin

section \<open> Operational Semantics \<close>

subsection \<open> Actions \<close>

datatype act = Tau | Local

lemma act_not_eq_iff[simp]:
  \<open>a \<noteq> Tau \<longleftrightarrow> a = Local\<close>
  \<open>a \<noteq> Local \<longleftrightarrow> a = Tau\<close>
  by (meson act.distinct act.exhaust)+

subsection \<open> Operational semantics steps \<close>

fun head_atoms :: \<open>'a comm \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) set\<close> where
  \<open>head_atoms (c1 ;; c2) = (let a1 = head_atoms c1
                             in if a1 = \<bottom> then head_atoms c2 else a1)\<close>
| \<open>head_atoms (c1 \<^bold>+ c2) = (head_atoms c1 \<squnion> head_atoms c2)\<close>
| \<open>head_atoms (c1 \<box> c2) = (head_atoms c1 \<squnion> head_atoms c2)\<close>
| \<open>head_atoms (c1 \<parallel> c2) = (head_atoms c1 \<squnion> head_atoms c2)\<close>
| \<open>head_atoms (Atomic b) = {b}\<close>
| \<open>head_atoms (DO c OD) = head_atoms c\<close>
| \<open>head_atoms Skip = {}\<close>
| \<open>head_atoms (\<mu> c) = head_atoms c\<close>
| \<open>head_atoms (FixVar x) = \<bottom>\<close>

inductive opstep :: \<open>act \<Rightarrow> 's \<times> 's comm \<Rightarrow> 's \<times> 's comm \<Rightarrow> bool\<close> where
  seq_left[intro!]: \<open>opstep a (h, c1) (h', c1') \<Longrightarrow> opstep a (h, c1 ;; c2) (h', c1' ;; c2)\<close>
| seq_right[intro!]: \<open>opstep Tau (h, Skip ;; c2) (h, c2)\<close>
| indet_left[intro]:  \<open>opstep a (h, c1) s' \<Longrightarrow> opstep a (h, c1 \<^bold>+ c2) s'\<close>
| indet_right[intro]: \<open>opstep a (h, c2) s' \<Longrightarrow> opstep a (h, c1 \<^bold>+ c2) s'\<close>
| endet_tau_left[intro]:  \<open>opstep Tau (h, c1) (h', c1') \<Longrightarrow> opstep Tau (h, c1 \<box> c2) (h', c1' \<box> c2)\<close>
| endet_tau_right[intro]: \<open>opstep Tau (h, c2) (h', c2') \<Longrightarrow> opstep Tau (h, c1 \<box> c2) (h', c1 \<box> c2')\<close>
| endet_skip_left[intro!]:  \<open>opstep Tau (h, Skip \<box> c2) (h, c2)\<close>
| endet_skip_right[intro!]: \<open>opstep Tau (h, c1 \<box> Skip) (h, c1)\<close>
| endet_local_left[intro]:  \<open>a \<noteq> Tau \<Longrightarrow> opstep a (h, c1) s' \<Longrightarrow> opstep a (h, c1 \<box> c2) s'\<close>
| endet_local_right[intro]: \<open>a \<noteq> Tau \<Longrightarrow> opstep a (h, c2) s' \<Longrightarrow> opstep a (h, c1 \<box> c2) s'\<close>
(* TODO
| par_left_tau[intro]: \<open>opstep Tau (h, Skip \<parallel> t) (h', t)\<close>
| par_right_tau[intro]: \<open>opstep a (h, s \<parallel> Skip) (h', s)\<close>
*)
| par_left[intro]: \<open>opstep a (h, s) (h', s') \<Longrightarrow> opstep a (h, s \<parallel> t) (h', s' \<parallel> t)\<close>
| par_right[intro]: \<open>opstep a (h, t) (h', t') \<Longrightarrow> opstep a (h, s \<parallel> t) (h', s \<parallel> t')\<close>
| par_skip[intro!]: \<open>opstep Tau (h, Skip \<parallel> Skip) (h, Skip)\<close>
| iter_step[intro]: \<open>opstep Tau (h, DO c OD) (h, c ;; DO c OD)\<close>
| iter_end[intro]: \<open>\<not> pre_state (\<Squnion>(head_atoms c)) h \<Longrightarrow> opstep Tau (h, DO c OD) (h, Skip)\<close>
| fixpt_skip[intro!]: \<open>c' = c[0 \<leftarrow> \<mu> c] \<Longrightarrow> opstep Tau (h, \<mu> c) (h, c')\<close>
| atomic[intro!]: \<open>a = Local \<Longrightarrow> snd s' = Skip \<Longrightarrow> b h (fst s') \<Longrightarrow> opstep a (h, Atomic b) s'\<close>

inductive_cases opstep_tauE[elim]: \<open>opstep Tau s s'\<close>
inductive_cases opstep_localE[elim]: \<open>opstep Local s s'\<close>

inductive_cases opstep_skipE[elim!]: \<open>opstep a (h, Skip) s'\<close>
inductive_cases opstep_seqE[elim]: \<open>opstep a (h, c1 ;; c2) s'\<close>
inductive_cases opstep_indetE[elim]: \<open>opstep a (h, c1 \<^bold>+ c2) s'\<close>
inductive_cases opstep_endetE[elim]: \<open>opstep a (h, c1 \<box> c2) s'\<close>
inductive_cases opstep_parE[elim]: \<open>opstep a (h, c1 \<parallel> c2) s'\<close>
inductive_cases opstep_iterE[elim]: \<open>opstep a (h, DO c OD) s'\<close>
inductive_cases opstep_fixptE[elim]: \<open>opstep a (h, \<mu> c) s'\<close>
inductive_cases opstep_atomicE[elim!]: \<open>opstep a (h, Atomic b) s'\<close>

paragraph \<open> Pretty operational semantics \<close>

abbreviation(input) pretty_opstep :: \<open>_ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> _\<close> (\<open>_ \<midarrow>(_)\<rightarrow> _\<close> [60,0,60] 60) where
  \<open>hs \<midarrow>a\<rightarrow> ht \<equiv> opstep a hs ht\<close>


subsection \<open> Lemmas about opstep \<close>

named_theorems opstep_iff

lemma opstep_iff_standard[opstep_iff]:
  \<open>opstep a (h, Skip) s' \<longleftrightarrow> False\<close>
  \<open>opstep a (h, c1 ;; c2) s' \<longleftrightarrow>
    a = Tau \<and> c1 = Skip \<and> s' = (h, c2) \<or>
    (\<exists>h' c1'. opstep a (h,c1) (h',c1') \<and> s' = (h', c1' ;; c2))\<close>
  \<open>opstep a (h, c1 \<^bold>+ c2) s' \<longleftrightarrow>
    opstep a (h, c1) s' \<or> opstep a (h, c2) s'\<close>
  \<open>opstep a (h, c1 \<box> c2) s' \<longleftrightarrow>
    a = Local \<and> opstep Local (h, c1) s' \<or>
    a = Local \<and> opstep Local (h, c2) s' \<or>
    a = Tau \<and> (\<exists>h' c1'. s' = (h', c1' \<box> c2) \<and> opstep Tau (h, c1) (h', c1')) \<or>
    a = Tau \<and> (\<exists>h' c2'. s' = (h', c1 \<box> c2') \<and> opstep Tau (h, c2) (h', c2')) \<or>
    a = Tau \<and> c1 = Skip \<and> s' = (h, c2) \<or>
    a = Tau \<and> c2 = Skip \<and> s' = (h, c1)\<close>
  \<open>opstep a (h, c1 \<parallel> c2) s' \<longleftrightarrow>
    a = Tau \<and> c1 = Skip \<and> c2 = Skip \<and> s' = (h, Skip) \<or>
    (\<exists>h' c1'. opstep a (h,c1) (h',c1') \<and> s' = (h', c1' \<parallel> c2)) \<or>
    (\<exists>h' c2'. opstep a (h,c2) (h',c2') \<and> s' = (h', c1 \<parallel> c2'))\<close>
  \<open>opstep a (h, DO c OD) s' \<longleftrightarrow>
    a = Tau \<and> \<not> pre_state (\<Squnion>(head_atoms c)) h \<and> s' = (h, Skip) \<or>
    a = Tau \<and> s' = (h, c ;; DO c OD)\<close>
  \<open>opstep a (h, \<mu> c) s' \<longleftrightarrow> a = Tau \<and> s' = (h, c[0 \<leftarrow> \<mu> c])\<close>
  \<open>opstep a (h, Atomic b) s' \<longleftrightarrow>
    a = Local \<and> snd s' = Skip \<and> b h (fst s')\<close>
         apply blast
        apply blast
       apply blast
      apply (rule iffI, (erule opstep_endetE; force), force)
     apply blast+
  done

lemma opstep_tau_preserves_heap:
  assumes \<open>s \<midarrow>Tau\<rightarrow> s'\<close>
  shows \<open>fst s' = fst s\<close>
proof -
  { fix a
    have \<open>s \<midarrow>a\<rightarrow> s' \<Longrightarrow> a = Tau \<Longrightarrow> fst s' = fst s\<close>
      by (induct rule: opstep.inducts) force+
  }
  then show ?thesis
    using assms by force
qed

lemma opstep_act_cases:
  \<open>s \<midarrow>a\<rightarrow> s' \<Longrightarrow>
    (a = Tau \<Longrightarrow> s \<midarrow>Tau\<rightarrow> s' \<Longrightarrow> fst s' = fst s \<Longrightarrow> P) \<Longrightarrow>
    (a = Local \<Longrightarrow> s \<midarrow>Local\<rightarrow> s' \<Longrightarrow> P) \<Longrightarrow>
    P\<close>
  by (metis (full_types) act.exhaust opstep_tau_preserves_heap)

lemma all_atom_comm_opstep:
  assumes
    \<open>opstep a (h, c) (h', c')\<close>
    \<open>all_atom_comm p c\<close>
  shows
    \<open>all_atom_comm p c'\<close>
proof -
  { fix s s'
    assume \<open>opstep a s s'\<close>
      and \<open>all_atom_comm p (snd s)\<close>
    then have \<open>all_atom_comm p (snd s')\<close>
      by (induct rule: opstep.inducts) force+
  }
  then show ?thesis
    using assms
    by (metis snd_conv)
qed

lemmas all_atom_comm_opstepD =
  all_atom_comm_opstep[rotated]


subsubsection \<open> adding parallel \<close>

lemma opstep_parallel_leftD:
  \<open>s \<midarrow>a\<rightarrow> s' \<Longrightarrow> (fst s, snd s \<parallel> cy) \<midarrow>a\<rightarrow> (fst s', snd s' \<parallel> cy)\<close>
  by (simp add: par_left)

lemma opstep_parallel_rightD:
  \<open>s \<midarrow>a\<rightarrow> s' \<Longrightarrow> (fst s, cx \<parallel> snd s) \<midarrow>a\<rightarrow> (fst s', cx \<parallel> snd s')\<close>
  by (simp add: par_right)


subsubsection \<open> iteraction with all_atom_comm \<close>

lemma opstep_preserves_all_atom_comm:
  assumes
    \<open>opstep a (h, c) (h', c')\<close>
    \<open>all_atom_comm p c\<close>
  shows \<open>all_atom_comm p c'\<close>
proof -
  { fix s s'
    have \<open>opstep a s s' \<Longrightarrow> all_atom_comm p (snd s) \<Longrightarrow> all_atom_comm p (snd s')\<close>
      by (induct arbitrary: h' rule: opstep.inducts) force+
  }
  then show ?thesis
    using assms
    by (metis snd_conv)
qed

lemmas rev_opstep_preserves_all_atom_comm = opstep_preserves_all_atom_comm[rotated]


subsection \<open> Opstep rules for defined programs \<close>

lemma opstep_guard[intro!]: \<open>p h \<Longrightarrow> opstep Local (h, Guard p) (h, Skip)\<close>
  by (force simp add: opstep.atomic pguard_def)

lemma opstep_IfThenElse_iff[opstep_iff]:
  \<open>opstep a (h, IfThenElse p ct cf) s' \<longleftrightarrow>
    a = Local \<and> p h \<and> s' = (h, Skip ;; ct) \<or> a = Local \<and> \<not> p h \<and> s' = (h, Skip ;; cf)\<close>
  by (simp add: IfThenElse_def opstep_iff)

lemma opstep_IfThenElse_true[intro]:
  \<open>p h \<Longrightarrow> opstep Local (h, IfThenElse p a b) (h, Skip ;; a)\<close>
  by (simp add: opstep_iff)

lemma opstep_IfThenElse_false[intro]:
  \<open>\<not> p h \<Longrightarrow> opstep Local (h, IfThenElse p a b) (h, Skip ;; b)\<close>
  by (simp add: opstep_iff)

lemma pre_state_passert_eq[simp]:
  \<open>pre_state (pguard p) = p\<close>
  by (simp add: pguard_def pre_state_def)

lemma opstep_WhileLoop_iff[opstep_iff]:
  \<open>opstep a (h, WhileLoop p c) s' \<longleftrightarrow>
    a = Tau \<and> s' = (h,
      (Guard p ;; c \<box> Guard (- p)) ;;
        DO Guard p ;; c \<box> Guard (- p) OD)\<close>
  by (simp add: WhileLoop_def opstep_iff)

end