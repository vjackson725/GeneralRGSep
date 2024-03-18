theory Soundness
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

inductive opstep :: \<open>act \<Rightarrow> ('l \<times> 's) \<times> ('l \<times> 's) comm \<Rightarrow> (('l \<times> 's) \<times> ('l \<times> 's) comm) \<Rightarrow> bool\<close> where
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


subsection \<open> Sugared atomic programs \<close>

definition \<open>passert p \<equiv> \<lambda>a b. p a \<and> a = b\<close>

abbreviation \<open>Assert p \<equiv> Atomic (passert p)\<close>
abbreviation \<open>Assume p \<equiv> Atomic (\<lambda>a. p)\<close>

lemmas Assert_def = arg_cong[where f=Atomic, OF meta_eq_to_obj_eq[OF passert_def]]

lemma passert_simps[simp]:
  \<open>passert p a b \<longleftrightarrow> p a \<and> b = a\<close>
  by (force simp add: passert_def)

lemma opstep_assert[intro!]: \<open>p h \<Longrightarrow> opstep Local (h, Assert p) (h, Skip)\<close>
  by (force simp add: opstep.atomic passert_def)

lemma opstep_assume[intro!]: \<open>q h' \<Longrightarrow> opstep Local (h, Assume q) (h', Skip)\<close>
  by (force simp add: opstep.atomic rel_liftR_def)

subsection \<open> If-then-else and While Loops \<close>

definition \<open>IfThenElse p ct cf \<equiv> Assert p ;; ct \<box> Assert (-p) ;; cf\<close>
definition \<open>WhileLoop p c \<equiv> \<mu> (Assert p ;; map_fixvar Suc c ;; FixVar 0 \<box> Assert (-p))\<close>

lemma IfThenElse_inject[simp]:
  \<open>IfThenElse p1 ct1 cf1 = IfThenElse p2 ct2 cf2 \<longleftrightarrow> p1 = p2 \<and> ct1 = ct2 \<and> cf1 = cf2\<close>
  by (simp add: IfThenElse_def passert_def fun_eq_iff, blast)

lemma WhileLoop_inject[simp]:
  \<open>WhileLoop p1 c1 = WhileLoop p2 c2 \<longleftrightarrow> p1 = p2 \<and> c1 = c2\<close>
  by (simp add: WhileLoop_def map_fixvar_inj_inject passert_def fun_eq_iff, blast)

lemma IfThenElse_distinct[simp]:
  \<open>IfThenElse p ct cf \<noteq> Skip\<close>
  \<open>IfThenElse p ct cf \<noteq> c1 ;; c2\<close>
  \<open>IfThenElse p ct cf \<noteq> c1 \<parallel> c2\<close>
  \<open>IfThenElse p ct cf \<noteq> \<mu> c\<close>
  \<open>IfThenElse p ct cf \<noteq> Atomic b\<close>
  \<open>Skip \<noteq> IfThenElse p ct cf\<close>
  \<open>c1 ;; c2 \<noteq> IfThenElse p ct cf\<close>
  \<open>c1 \<parallel> c2 \<noteq> IfThenElse p ct cf\<close>
  \<open>\<mu> c \<noteq> IfThenElse p ct cf\<close>
  \<open>Atomic b \<noteq> IfThenElse p ct cf\<close>
  by (simp add: IfThenElse_def)+

lemma WhileLoop_distinct[simp]:
  \<open>WhileLoop p c \<noteq> Skip\<close>
  \<open>WhileLoop p c \<noteq> c1 \<box> c2\<close>
  \<open>WhileLoop p c \<noteq> c1 \<parallel> c2\<close>
  \<open>WhileLoop p c \<noteq> Atomic b\<close>
  \<open>Skip \<noteq> WhileLoop p c\<close>
  \<open>c1 \<box> c2 \<noteq> WhileLoop p c\<close>
  \<open>c1 \<parallel> c2 \<noteq> WhileLoop p c\<close>
  \<open>Atomic b \<noteq> WhileLoop p c\<close>
  \<open>WhileLoop p c \<noteq> \<mu> c\<close>
  \<open>\<mu> c \<noteq> WhileLoop p c\<close>
           apply (simp add: WhileLoop_def; fail)+
   apply (rule size_neq_size_imp_neq, simp add: WhileLoop_def)+
  done


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

lemma opstep_WhileLoop_iff[opstep_iff]:
  \<open>opstep a (h, WhileLoop p c) s' \<longleftrightarrow>
    a = Tau \<and> s' = (h, Assert p ;; map_fixvar Suc c ;; WhileLoop p c \<box> Assert (- p))\<close>
  by (simp add: WhileLoop_def opstep_iff fixvar_subst_over_map_avoid)


section \<open> Safe \<close>

inductive safe
  :: \<open>nat \<Rightarrow> ('l::perm_alg \<times> 's::perm_alg) comm \<Rightarrow>
      'l \<Rightarrow> 's \<Rightarrow> ('s \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow> ('s \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow> ('l \<times> 's \<Rightarrow> bool) \<Rightarrow> bool\<close>
  where
  safe_nil[intro!]: \<open>safe 0 c hl hs r g q\<close>
| safe_suc[intro]:
  \<open>\<comment> \<open> if the command is Skip, the postcondition is established \<close>
    \<comment> \<open> TODO: This requires termination is represented as infinite stuttering past the end.
               We may want a different model, but that would be more complicated. \<close>
    (c = Skip \<longrightarrow> q (hl, hs)) \<Longrightarrow>
    \<comment> \<open> rely steps are safe \<close>
    (\<And>hs'. r hs hs' \<Longrightarrow> safe n c hl hs' r g q) \<Longrightarrow>
    \<comment> \<open> opsteps are safe \<close>
    (\<And>a c' hx'.
        ((hl, hs), c) \<midarrow>a\<rightarrow> (hx', c') \<Longrightarrow>
        (a = Local \<longrightarrow> g hs (snd hx')) \<and>
        safe n c' (fst hx') (snd hx') r g q) \<Longrightarrow>
    \<comment> \<open> opsteps are frame closed and establish the guarantee \<close>
    (\<And>a c' hlf hx'.
        ((hl + hlf, hs), c) \<midarrow>a\<rightarrow> (hx', c') \<Longrightarrow>
        hl ## hlf \<Longrightarrow>
        (a = Local \<longrightarrow> g hs (snd hx')) \<and>
        (\<exists>hl'.
          hl' ## hlf \<and> fst hx' = hl' + hlf \<and>
          (a = Tau \<longrightarrow> hl' = hl) \<and>
          safe n c' hl' (snd hx') r g q)) \<Longrightarrow>
    \<comment> \<open> conclude a step can be made \<close>
    safe (Suc n) c hl hs r g q\<close>

subsection \<open> Proofs about safe \<close>

inductive_cases safe_zeroE[elim!]: \<open>safe 0 c hl hs r g q\<close>
inductive_cases safe_sucE[elim]: \<open>safe (Suc n) c hl hs r g q\<close>

lemma safe_nil_iff[simp]:
  \<open>safe 0 c hl hs r g q \<longleftrightarrow> True\<close>
  by force

lemma safe_suc_iff:
  \<open>safe (Suc n) c hl hs r g q \<longleftrightarrow>
    (c = Skip \<longrightarrow> q (hl, hs)) \<and>
    (\<forall>hs'. r hs hs' \<longrightarrow> safe n c hl hs' r g q) \<and>
    (\<forall>a c' hx'.
        ((hl, hs), c) \<midarrow>a\<rightarrow> (hx', c') \<longrightarrow>
        (a = Local \<longrightarrow> g hs (snd hx')) \<and>
        safe n c' (fst hx') (snd hx') r g q) \<and>
    (\<forall>a c' hlf hx'.
        ((hl + hlf, hs), c) \<midarrow>a\<rightarrow> (hx', c') \<longrightarrow>
        hl ## hlf \<longrightarrow>
        (a = Local \<longrightarrow> g hs (snd hx')) \<and>
        (\<exists>hl'.
          hl' ## hlf \<and> fst hx' = hl' + hlf \<and>
          (a = Tau \<longrightarrow> hl' = hl) \<and>
          safe n c' hl' (snd hx') r g q))\<close>
  apply (rule iffI)
   apply (erule safe_sucE, (simp; fail))
  apply (rule safe_suc; presburger)
  done

lemma safe_sucD:
  \<open>safe (Suc n) c hl hs r g q \<Longrightarrow> c = Skip \<Longrightarrow> q (hl, hs)\<close>
  \<open>safe (Suc n) c hl hs r g q \<Longrightarrow> r hs hs' \<Longrightarrow> safe n c hl hs' r g q\<close>
  \<open>safe (Suc n) c hl hs r g q \<Longrightarrow> ((hl, hs), c) \<midarrow>a\<rightarrow> (hx', c') \<Longrightarrow> safe n c' (fst hx') (snd hx') r g q\<close>
  \<open>safe (Suc n) c hl hs r g q \<Longrightarrow> ((hl, hs), c) \<midarrow>Local\<rightarrow> (hx', c') \<Longrightarrow> g hs (snd hx')\<close>
  \<open>safe (Suc n) c hl hs r g q \<Longrightarrow>
      ((hl + hlf, hs), c) \<midarrow>a\<rightarrow> (hx', c') \<Longrightarrow>
      hl ## hlf \<Longrightarrow>
      (a = Local \<longrightarrow> g hs (snd hx')) \<and>
      (\<exists>hl'.
        hl' ## hlf \<and> fst hx' = hl' + hlf \<and>
        (a = Tau \<longrightarrow> hl' = hl) \<and>
        safe n c' hl' (snd hx') r g q)\<close>
  by (erule safe_sucE, simp; fail)+


subsubsection \<open> Monotonicity of safe \<close>

lemma safe_postpred_monoD:
  \<open>safe n c hl hs r g q \<Longrightarrow> q \<le> q' \<Longrightarrow> safe n c hl hs r g q'\<close>
  apply (induct rule: safe.induct)
   apply blast
  apply (rule safe_suc)
      apply (clarsimp simp add: le_fun_def; fail)+
  apply metis
  done

lemmas safe_postpred_mono = safe_postpred_monoD[rotated]

lemma safe_guarantee_monoD:
  \<open>safe n c hl hs r g q \<Longrightarrow> g \<le> g' \<Longrightarrow> safe n c hl hs r g' q\<close>
proof (induct rule: safe.induct)
  case safe_nil
  then show ?case by blast
next
  case (safe_suc c q hl hs r n g)
  show ?case
    using safe_suc.prems
    apply -
    apply (rule safe.safe_suc)
       apply (simp add: safe_suc.hyps; fail)
      apply (blast intro: safe_suc.hyps)
     apply (metis predicate2D safe_suc.hyps(4))
    apply (simp add: le_fun_def, fast dest: safe_suc.hyps(5))
    done
qed

lemmas safe_guarantee_mono = safe_guarantee_monoD[rotated]

lemma safe_rely_antimonoD:
  \<open>safe n c hl hs r g q \<Longrightarrow> r' \<le> r \<Longrightarrow> safe n c hl hs r' g q\<close>
  apply (induct rule: safe.induct)
   apply force
  apply (rule safe_suc)
        apply presburger
       apply (metis predicate2D)
    apply presburger+
  apply metis
  done

lemmas safe_rely_antimono = safe_rely_antimonoD[rotated]

lemma safe_step_monoD:
  \<open>safe n c hl hs r g q \<Longrightarrow> m \<le> n \<Longrightarrow> safe m c hl hs r g q\<close>
  apply (induct arbitrary: m rule: safe.inducts)
   apply force
  apply (clarsimp simp add: le_Suc_iff0)
  apply (erule disjE, fast)
  apply clarsimp
  apply (rule safe_suc)
        apply (clarsimp; metis)+
  done


subsection \<open> Safety of Skip \<close>

lemma safe_skip':
  \<open>sswa r q (hl, hs) \<Longrightarrow> safe n Skip hl hs r g (sswa r q)\<close>
  apply (induct n arbitrary: hl hs q)
   apply force
  apply (rule safe_suc)
        apply blast
       apply (simp add: weak_framed_subresource_rel_def all_conj_distrib sp_def)
       apply (meson opstep_skipE rtranclp.rtrancl_into_rtrancl; fail)
      apply blast+
  done

lemma safe_skip:
  \<open>p (hl, hs) \<Longrightarrow> sswa r p \<le> q \<Longrightarrow> safe n Skip hl hs r g q\<close>
  apply (rule safe_postpred_monoD[OF safe_skip'[where q=p]])
   apply (metis (mono_tags, lifting) rel_Times_iff rtranclp.rtrancl_refl sp_def)
  apply blast
  done


subsection \<open> Safety of Atomic \<close>

lemma safe_atom':
  \<open>sp b (wlp ((=) \<times>\<^sub>R r\<^sup>*\<^sup>*) p) \<le> sswa r q \<Longrightarrow>
    \<forall>f. sp b (wlp ((=) \<times>\<^sub>R r\<^sup>*\<^sup>*) (p \<^emph>\<and> f)) \<le> sswa r (q \<^emph>\<and> f) \<Longrightarrow>
    b \<le> \<top> \<times>\<^sub>R g \<Longrightarrow>
    wlp ((=) \<times>\<^sub>R r\<^sup>*\<^sup>*) p (hl, hs) \<Longrightarrow>
    safe n (Atomic b) hl hs r g (sswa r q)\<close>
proof (induct n arbitrary: hl hs)
  case 0
  then show ?case by force
next
  case (Suc n)
  show ?case
    using Suc.prems
    apply (intro safe.safe_suc)
      (* subgoal: skip *)
          apply force
      (* subgoal: rely *)
         apply (rule Suc.hyps; force simp add: wlp_rely_step_rtranclp)
      (* subgoal: plain opstep *)
     apply (simp add: opstep_iff del: top_apply sup_apply)
     apply (rule conjI)
      apply (metis predicate2D prod.collapse rel_Times_iff)
     apply (rule safe_skip[where p=\<open>sswa r q\<close>])
      apply (simp del: sup_apply, blast)
     apply (force simp add: sp_rely_absorb)
      (* subgoal: local framed opstep *)
    apply (clarsimp simp add: opstep_iff sp_def[of b] imp_ex_conjL le_fun_def simp del: sup_apply)
    apply (drule_tac x=\<open>(=) hlf \<times>\<^sub>P \<top>\<close> in spec, drule spec2, drule spec2, drule mp, fast, drule mp,
        rule predicate1D[OF wlp_rely_sepconj_conj_semidistrib])
     apply (rule sepconj_conjI; force)
    apply (drule predicate1D[OF sp_rely_sepconj_conj_semidistrib])
    apply (clarsimp simp add: sepconj_conj_def)
    apply (metis safe_skip')
    done
qed

lemma safe_atom:
  \<open>sp b (wssa r p) \<le> sswa r q \<Longrightarrow>
    \<forall>f. sp b (wssa r (p \<^emph>\<and> f)) \<le> sswa r (q \<^emph>\<and> f) \<Longrightarrow>
    b \<le> \<top> \<times>\<^sub>R g \<Longrightarrow>
    wssa r p (hl, hs) \<Longrightarrow>
    sswa r q \<le> q' \<Longrightarrow>
    safe n (Atomic b) hl hs r g q'\<close>
  by (meson safe_postpred_mono safe_atom')


subsection \<open> Safety of Sequencing \<close>

lemma safe_seq_assoc_left:
  \<open>safe n c hl hs r g q \<Longrightarrow>
    c = (c1 ;; c2 ;; c3) \<Longrightarrow>
    safe n ((c1 ;; c2) ;; c3) hl hs r g q\<close>
  apply (induct arbitrary: c1 c2 c3 rule: safe.inducts)
   apply force
  apply (rule safe_suc)
     apply blast
    apply blast
   apply (clarsimp simp add: opstep_iff, metis)+
  done

lemma safe_seq_assoc_right:
  \<open>safe n c hl hs r g q \<Longrightarrow>
    c = ((c1 ;; c2) ;; c3) \<Longrightarrow>
    safe n (c1 ;; c2 ;; c3) hl hs r g q\<close>
  apply (induct arbitrary: c1 c2 c3 rule: safe.inducts)
   apply force
  apply (rule safe_suc)
     apply blast
    apply blast
   apply (clarsimp simp add: opstep_iff, metis)+
  done

lemma safe_seq':
  \<open>safe n c1 hl hs r g q \<Longrightarrow>
    (\<forall>m\<le>n. \<forall>hl' hs'. q (hl', hs') \<longrightarrow> safe m c2 hl' hs' r g q') \<Longrightarrow>
    safe n (c1 ;; c2) hl hs r g q'\<close>
proof (induct arbitrary: c2 q' rule: safe.inducts)
  case (safe_suc c q hl hs r n g)

  have safe_c2:
    \<open>\<And>m hl' hs'. m \<le> n \<Longrightarrow> q (hl', hs') \<Longrightarrow> safe m c2 hl' hs' r g q'\<close>
    \<open>\<And>hl' hs'. q (hl', hs') \<Longrightarrow> safe (Suc n) c2 hl' hs' r g q'\<close>
    using safe_suc.prems
    by force+
  then show ?case
    using safe_suc.prems(1) safe_suc.hyps(1)
    apply -
    apply (rule safe.safe_suc)
       apply force
      (* subgoal: rely *)
      apply (simp add: safe_suc.hyps(3); fail)
      (* subgoal: plain opstep *)
     apply (clarsimp simp add: opstep_iff simp del: sup_apply)
     apply (elim disjE conjE exE)
      apply (force dest: reflp_onD)
     apply (frule safe_suc.hyps(4))
     apply (clarsimp simp del: sup_apply)
      (* subgoal: local framed opstep *)
    apply (clarsimp simp add: opstep_iff simp del: sup_apply)
    apply (erule disjE, force)
    apply (clarsimp simp del: sup_apply)
    apply (metis safe_c2(1) safe_suc.hyps(5) fst_conv snd_conv)
    done
qed force


lemma safe_seq:
  \<open>safe n c1 hl hs r g q \<Longrightarrow>
    (\<forall>hl' hs'. q (hl', hs') \<longrightarrow> safe n c2 hl' hs' r g q') \<Longrightarrow>
    safe n (c1 ;; c2) hl hs r g q'\<close>
  by (force intro: safe_seq' safe_step_monoD)


subsection \<open> Safety of Iter \<close>

lemma safe_iter:
  \<open>(\<And>hl' hs'. sswa r i (hl', hs') \<Longrightarrow> safe n c hl' hs' r g (sswa r i)) \<Longrightarrow>
    sswa r i (hl, hs) \<Longrightarrow>
    safe n (Iter c) hl hs r g (sswa r i)\<close>
proof (induct n arbitrary: i hl hs)
  case (Suc n)

  have safe_ih:
    \<open>\<And>m hl' hs'. m \<le> n \<Longrightarrow> sswa r i (hl', hs') \<Longrightarrow> safe m c hl' hs' r g (sswa r i)\<close>
    \<open>\<And>hl' hs'. sswa r i (hl', hs') \<Longrightarrow> safe (Suc n) c hl' hs' r g (sswa r i)\<close>
    using Suc.prems(1)
    by (force intro: safe_step_monoD)+

  note safe_suc_c = safe_sucD[OF safe_ih(2)]

  show ?case
    using Suc.prems(2)
    apply -
    apply (rule safe.safe_suc)
      (* subgoal: skip *)
       apply blast
      (* subgoal: rely *)
      apply (rule Suc.hyps)
       apply (simp add: safe_ih(1); fail)
      apply (metis sp_rely_step_rtranclp)
      (* subgoal: plain opstep *)
     apply (clarsimp simp add: le_Suc_eq all_conj_distrib opstep_iff)
     apply (erule disjE)
      apply (simp add: rely_rel_wlp_impl_sp safe_skip'; fail)
     apply clarsimp
     apply (rule safe_seq')
      apply (rule safe_ih(1))
       apply blast
      apply (simp add: rely_rel_wlp_impl_sp; fail)
     apply clarsimp
     apply (rule safe_step_monoD[rotated], assumption)
     apply (simp add: Suc.hyps safe_ih(1); fail)
      (* subgoal: locally framed opstep *)
    apply (clarsimp simp add: le_Suc_eq all_conj_distrib opstep_iff simp del: sup_apply)
    apply (erule disjE)
     apply (simp add: rely_rel_wlp_impl_sp safe_skip'; fail)
    apply clarsimp
    apply (rule safe_seq')
     apply (rule safe_ih(1))
      apply blast
     apply (simp add: rely_rel_wlp_impl_sp; fail)
    apply clarsimp
    apply (rule safe_step_monoD[rotated], assumption)
    apply (simp add: Suc.hyps safe_ih(1); fail)
    done
qed force


subsubsection \<open> Safety of internal nondeterminism \<close>

lemma safe_indet:
    \<open>safe n c1 hl hs r g q \<Longrightarrow>
      safe n c2 hl hs r g q \<Longrightarrow>
      safe n (c1 \<^bold>+ c2) hl hs r g q\<close>
proof (induct n arbitrary: c1 c2 hl hs)
  case 0
  then show ?case by blast
next
  case (Suc n)

  have safeSuc:
    \<open>safe (Suc n) c1 hl hs r g q\<close>
    \<open>safe (Suc n) c2 hl hs r g q\<close>
    using Suc.prems
    by simp+
  note safe_suc1 = safe_sucD[OF safeSuc(1)]
  note safe_suc2 = safe_sucD[OF safeSuc(2)]

  have
    \<open>\<forall>m\<le>n. safe m c1 hl hs r g q\<close>
    \<open>\<forall>m\<le>n. safe m c2 hl hs r g q\<close>
    using Suc.prems
    by (meson le_SucI safe_step_monoD)+
  then show ?case
    apply -
    apply (rule safe_suc)
       apply blast
      (* subgoal: rely *)
      apply (metis Suc.hyps safe_suc1(2) safe_suc2(2))
      (* subgoal: plain opstep *)
     apply (clarsimp simp add: opstep_iff simp del: sup_apply)
     apply (elim disjE conjE exE)
      apply (force dest: safe_suc1(3,4))
     apply (force dest: safe_suc2(3,4))
      (* subgoal: local frame opstep *)
    apply (clarsimp simp add: opstep_iff simp del: sup_apply)
    apply (elim disjE conjE exE)
     apply (erule opstep_act_cases; metis safe_suc1(5) fst_conv snd_conv)
    apply (erule opstep_act_cases; metis safe_suc2(5) fst_conv snd_conv)
    done
qed


subsubsection \<open> Safety of external nondeterminism \<close>

lemma safe_endet:
    \<open>safe n c1 hl hs r g q \<Longrightarrow>
      safe n c2 hl hs r g q \<Longrightarrow>
      safe n (c1 \<box> c2) hl hs r g q\<close>
proof (induct n arbitrary: c1 c2 hl hs)
  case 0
  then show ?case by blast
next
  case (Suc n)

  have safeSuc:
    \<open>safe (Suc n) c1 hl hs r g q\<close>
    \<open>safe (Suc n) c2 hl hs r g q\<close>
    using Suc.prems
    by simp+
  note safe_suc1 = safe_sucD[OF safeSuc(1)]
  note safe_suc2 = safe_sucD[OF safeSuc(2)]

  have
    \<open>\<forall>m\<le>n. safe m c1 hl hs r g q\<close>
    \<open>\<forall>m\<le>n. safe m c2 hl hs r g q\<close>
    using Suc.prems
    by (meson le_SucI safe_step_monoD)+
  then show ?case
    apply -
    apply (rule safe_suc)
       apply blast
      (* subgoal: rely *)
      apply (metis Suc.hyps safe_suc1(2) safe_suc2(2))
      (* subgoal: plain opstep *)
     apply (clarsimp simp add: opstep_iff simp del: sup_apply)
     apply (elim disjE conjE exE)
          apply (force dest: safe_suc1(3,4))
         apply (force dest: safe_suc2(3,4))
        apply (frule opstep_tau_preserves_heap, clarsimp)
        apply (fastforce intro: Suc.hyps dest: safe_suc1(3))
       apply (frule opstep_tau_preserves_heap, clarsimp)
       apply (fastforce intro: Suc.hyps dest: safe_suc2(3))
      apply blast
     apply blast
      (* subgoal: local frame opstep *)
    apply (clarsimp simp add: opstep_iff simp del: sup_apply)
    apply (elim disjE conjE exE)
         apply (erule opstep_act_cases; metis safe_suc1(5) fst_conv snd_conv)
        apply (erule opstep_act_cases; metis safe_suc2(5) fst_conv snd_conv)
      (* subsubgoal: left tau passthrough *)
       apply (frule safe_suc1(5), blast)
       apply clarsimp
       apply (frule opstep_tau_preserves_heap)
       apply (clarsimp simp del: sup_apply)
       apply (metis Suc.hyps order.refl)
      (* subsubgoal: right tau passthrough *)
      apply (frule safe_suc2(5), blast)
      apply clarsimp
      apply (frule opstep_tau_preserves_heap)
      apply (clarsimp simp del: sup_apply)
      apply (metis Suc.hyps order.refl)
      (* subsubgoal: right skip tau *)
     apply blast
      (* subsubgoal: left skip tau *)
    apply blast
    done
qed


subsection \<open> Safety of frame \<close>

lemma safe_frame':
  \<open>safe n c hl hs r g q \<Longrightarrow>
    hl ## hlf \<Longrightarrow>
    sp ((=) \<times>\<^sub>R (r \<squnion> g)\<^sup>*\<^sup>*) f (hlf, hs) \<Longrightarrow>
    safe n c (hl + hlf) hs r g (q \<^emph>\<and> sp ((=) \<times>\<^sub>R (r \<squnion> g)\<^sup>*\<^sup>*) f)\<close>
proof (induct arbitrary: hlf rule: safe.induct)
  case (safe_nil c hl hs r g q)
  then show ?case by blast
next
  case (safe_suc c q hl hs r n g)

  show ?case
    using safe_suc.prems
    apply -
    apply (rule safe.safe_suc)
      (* subgoal: skip *)
       apply (clarsimp simp add: sepconj_conj_def simp del: sup_apply)
       apply (drule mp[OF safe_suc.hyps(1)])
       apply blast
      (* subgoal: rely step *)
      apply (metis safe_suc.hyps(3) sup2I1 sp_rely_step_rtranclp)
      (* subgoal: plain opstep *)
     apply (frule safe_suc.hyps(5), blast)
     apply (clarsimp simp del: sup_apply top_apply)
     apply (metis fst_conv opstep_act_cases snd_eqD sp_rely_step_rtranclp sup2I2)
      (* subgoal: local framed opstep *)
    apply (clarsimp simp add: partial_add_assoc2[of hl hlf] simp del: sup_apply top_apply)
    apply (rename_tac hlf2 hl'hlfhlf2 hs')
    apply (frule safe_suc.hyps(5), metis disjoint_add_swap_lr)
    apply (clarsimp simp del: sup_apply top_apply)
    apply (intro exI conjI)
       prefer 2 (* instantiating a schematic *)
       apply (rule partial_add_assoc[symmetric])
         apply (metis disjoint_add_leftR disjoint_add_rightL)
        apply (metis disjoint_add_leftR)
       apply (metis disjoint_add_leftR disjoint_add_rightR)
      apply (metis disjoint_add_leftR disjoint_add_swap_rl)
     apply blast
    apply (metis disjoint_add_leftR disjoint_add_rightL fst_eqD opstep_act_cases snd_eqD
        sp_rely_step_rtranclp sup2I2)
    done
qed

lemma safe_frame:
  \<open>safe n c hl hs r g q \<Longrightarrow>
    hl ## hlf \<Longrightarrow>
    f (hlf, hs) \<Longrightarrow>
    sp ((=) \<times>\<^sub>R (r \<squnion> g)\<^sup>*\<^sup>*) f \<le> f' \<Longrightarrow>
    safe n c (hl + hlf) hs r g (q \<^emph>\<and> f')\<close>
  apply (rule safe_postpred_monoD)
   apply (rule safe_frame'[where f=f]; blast)
  apply (blast dest: sepconj_conj_monoR)
  done


subsection \<open> Safety of parallel \<close>

lemma safe_parallel':
  \<open>safe n c1 hl1 hs (r \<squnion> g2) g1 (sp ((=) \<times>\<^sub>R (r \<squnion> g2)\<^sup>*\<^sup>*) q1) \<Longrightarrow>
    safe n c2 hl2 hs (r \<squnion> g1) g2 (sp ((=) \<times>\<^sub>R (r \<squnion> g1)\<^sup>*\<^sup>*) q2) \<Longrightarrow>
    hl1 ## hl2 \<Longrightarrow>
    safe n (c1 \<parallel> c2) (hl1 + hl2) hs r (g1 \<squnion> g2)
      ((sp ((=) \<times>\<^sub>R (r \<squnion> g2)\<^sup>*\<^sup>*) q1) \<^emph>\<and> (sp ((=) \<times>\<^sub>R (r \<squnion> g1)\<^sup>*\<^sup>*) q2))\<close>
proof (induct n arbitrary: c1 c2 hl1 hl2 hs)
  case 0
  then show ?case by force
next
  case (Suc n)

  note safe_suc1 = safe_sucD[OF Suc.prems(1)]
  note safe_suc2 = safe_sucD[OF Suc.prems(2)]

  have
    \<open>\<forall>m\<le>n. safe m c1 hl1 hs (r \<squnion> g2) g1 (sp ((=) \<times>\<^sub>R (r \<squnion> g2)\<^sup>*\<^sup>*) q1)\<close>
    \<open>\<forall>m\<le>n. safe m c2 hl2 hs (r \<squnion> g1) g2 (sp ((=) \<times>\<^sub>R (r \<squnion> g1)\<^sup>*\<^sup>*) q2)\<close>
     apply (metis Suc.prems(1) le_Suc_eq safe_step_monoD)
    apply (metis Suc.prems(2) le_Suc_eq safe_step_monoD)
    done
  then show ?case
    using Suc.hyps Suc.prems(3-)
    apply -
    apply (rule safe_suc)
       apply blast
      apply (metis safe_suc1(2) safe_suc2(2) sup2CI)
    subgoal
      apply (simp add: opstep_iff del: sup_apply)
      apply (elim disjE conjE exE)
        (* subgoal: tau *)
        apply (rule conjI)
         apply blast
        apply (clarsimp simp del: sup_apply)
        apply (insert safe_suc1(1) safe_suc2(1))
        apply (clarsimp simp del: sup_apply)
        apply (rule safe_skip[of \<open>sp ((=) \<times>\<^sub>R (r \<squnion> g2)\<^sup>*\<^sup>*) q1 \<^emph>\<and> sp ((=) \<times>\<^sub>R (r \<squnion> g1)\<^sup>*\<^sup>*) q2\<close>])
         apply (clarsimp simp add: sepconj_conj_def[of \<open>sp _ _\<close>] simp del: sup_apply)
         apply blast
        apply (rule sp_rely_sepconj_conj_semidistrib_mono)
         apply (clarsimp simp add: sp_comp_rel simp del: sup_apply; fail)
        apply (clarsimp simp add: sp_comp_rel simp del: sup_apply; fail)
        (* subgoal: left *)
       apply (frule safe_suc1(5), force)
       apply (clarsimp simp del: sup_apply)
       apply (rule conjI, force)
       apply (erule opstep_act_cases)
        apply (metis add_le_imp_le_left add_le_mono1 fstI le_numeral_extra(3) snd_eqD)
       apply (metis safe_suc2(2) sup2CI)
        (* subgoal: right *)
      apply (clarsimp simp add: partial_add_commute[of hl1] simp del: sup_apply)
      apply (frule safe_suc2(5), metis disjoint_sym)
      apply (clarsimp simp add: partial_add_commute[symmetric, of hl1] disjoint_sym_iff
          simp del: sup_apply)
      apply (erule opstep_act_cases)
       apply (simp; fail)
      apply (clarsimp simp del: top_apply)
      apply (metis safe_suc1(2) sup2CI disjoint_sym)
      done
    subgoal
      apply (simp add: opstep_iff del: top_apply sup_apply)
      apply (elim disjE conjE exE)
        (* subgoal: tau *)
        apply (rule conjI, blast)
        apply (clarsimp simp del: top_apply sup_apply)
        apply (insert safe_suc1(1) safe_suc2(1))
        apply (clarsimp simp del: top_apply sup_apply)
        apply (rule safe_skip[of \<open>sp ((=) \<times>\<^sub>R (r \<squnion> g2)\<^sup>*\<^sup>*) q1 \<^emph>\<and> sp ((=) \<times>\<^sub>R (r \<squnion> g1)\<^sup>*\<^sup>*) q2\<close>])
         apply (clarsimp simp add: sepconj_conj_def[of \<open>sp _ _\<close>] simp del: top_apply sup_apply)
         apply blast
        apply (rule sp_rely_sepconj_conj_semidistrib_mono)
         apply (simp add: sp_comp_rel; fail)
        apply (simp add: sp_comp_rel; fail)
          (* subgoal: left *)
       apply (simp add: partial_add_assoc2[of hl1] disjoint_sym_iff del: top_apply sup_apply)
       apply (frule safe_suc1(5))
        apply (metis disjoint_add_swap_lr disjoint_sym_iff)
       apply (clarsimp simp del: top_apply sup_apply)
       apply (rule conjI, blast)
       apply (rule_tac x=\<open>_ + _\<close> in exI)
       apply (intro conjI)
          apply (rule disjoint_add_swap_rl[rotated], fast)
          apply (metis disjoint_add_leftR disjoint_sym_iff)
         apply (metis disjoint_add_leftR disjoint_sym partial_add_assoc3)
        apply blast
       apply (erule opstep_act_cases, force)
       apply (metis disjoint_add_rightL disjoint_add_rightR disjoint_sym_iff safe_suc2(2) sup2CI)
        (* subgoal right *)
      apply (simp add: partial_add_commute[of hl1] partial_add_assoc2[of hl2] disjoint_sym_iff
          del: top_apply sup_apply)
      apply (frule safe_suc2(5))
       apply (metis disjoint_add_swap_lr disjoint_sym_iff)
      apply (clarsimp simp del: top_apply sup_apply)
      apply (rule conjI, force)
      apply (rule_tac x=\<open>_ + _\<close> in exI)
      apply (intro conjI)
         apply (rule disjoint_add_swap_rl[rotated], fast)
         apply (metis disjoint_add_leftR disjoint_sym_iff)
        apply (metis disjoint_add_leftR disjoint_sym partial_add_assoc3)
       apply blast
      apply (simp add: partial_add_commute[of _ hl1] disjoint_sym_iff del: top_apply sup_apply)
      apply (subst partial_add_commute, metis disjoint_add_leftL disjoint_sym)
      apply (erule opstep_act_cases, (simp; fail))
      apply (metis disjoint_add_rightL disjoint_sym_iff safe_suc1(2) sup2CI)
      done
    done
qed

lemma safe_parallel:
  \<open>safe n c1 hl1 hs (r \<squnion> g2) g1 (sp ((=) \<times>\<^sub>R (r \<squnion> g2)\<^sup>*\<^sup>*) q1) \<Longrightarrow>
    safe n c2 hl2 hs (r \<squnion> g1) g2 (sp ((=) \<times>\<^sub>R (r \<squnion> g1)\<^sup>*\<^sup>*) q2) \<Longrightarrow>
    hl1 ## hl2 \<Longrightarrow>
    sp ((=) \<times>\<^sub>R (r \<squnion> g2)\<^sup>*\<^sup>*) q1 \<^emph>\<and> sp ((=) \<times>\<^sub>R (r \<squnion> g1)\<^sup>*\<^sup>*) q2 \<le> q \<Longrightarrow>
    g1 \<squnion> g2 \<le> g \<Longrightarrow>
    safe n (c1 \<parallel> c2) (hl1 + hl2) hs r g q\<close>
  by (meson safe_guarantee_monoD safe_parallel' safe_postpred_mono)


subsection \<open> Safety of conj \<close>

lemma safe_conj:
  fixes hl :: \<open>'a :: perm_alg\<close>
  shows
  \<open>safe n c hl hs r g q1 \<Longrightarrow>
    safe n c hl hs r g q2 \<Longrightarrow>
    \<forall>a b c::'a. a ## c \<longrightarrow> b ## c \<longrightarrow> a + c = b + c \<longrightarrow> a = b \<Longrightarrow>
    safe n c hl hs r g (q1 \<sqinter> q2)\<close>
proof (induct n arbitrary: c hl hs r g q1 q2)
  case 0
  then show ?case by blast
next
  case (Suc n)

  show ?case
    using Suc.prems
    apply -
    apply (intro safe_suc conjI impI allI)
         apply blast
        apply (rule Suc.hyps; meson safe_sucD; fail)
       apply (meson safe_sucD; fail)
      apply (rule Suc.hyps; meson safe_sucD; fail)
     apply (meson safe_sucD; fail)

    apply (drule safe_sucD(5), blast, blast)
    apply (drule safe_sucD(5), blast, blast)
    apply (case_tac a)
     apply (clarsimp simp del: inf_apply)
     apply (rule Suc.hyps; blast)
    apply (clarsimp simp del: inf_apply)
    apply (rename_tac hs' hl'1 hl'2)
    apply (rule exI, rule conjI, assumption, rule conjI, rule refl)
    apply (drule spec2, drule mp, assumption, drule spec, drule mp, assumption,
        drule mp, assumption)
    apply (simp add: Suc.hyps Suc.prems(3))
    done
qed


section \<open> Soundness \<close>

lemma soundness:
  assumes \<open>rgsat c r g p q\<close>
    and \<open>p (hl, hs)\<close>
  shows \<open>safe n c hl hs r g q\<close>
  using assms
proof (induct c r g p q arbitrary: n hl hs rule: rgsat.inducts)
  case (rgsat_skip p r q g as h)
  then show ?case
    by (simp add: safe_skip)
next
  case (rgsat_seq c1 r g p1 p2 c2 p3)
  then show ?case
    using safe_seq[of n c1 hl hs r g p2 c2 p3]
    by blast
next
  case (rgsat_indet c1 r g1 p q1 c2 g2 q2 g q)
  then show ?case
    using safe_indet[of n c1 hl hs r g q c2]
    by (meson safe_guarantee_mono safe_postpred_mono)
next
  case (rgsat_endet c1 r g1 p q1 c2 g2 q2 g q)
  then show ?case
    using safe_endet[of n c1 hl hs r g q c2]
    by (meson safe_guarantee_mono safe_postpred_mono)
next
  case (rgsat_parallel s1 r g2 g1 p1 q1 s2 p2 q2 g q1' q2')
  then show ?case
    apply -
    apply (clarsimp simp add: sepconj_conj_def[of p1 p2] le_fun_def[of p] simp del: sup_apply)
    apply (rule safe_parallel[where ?q1.0=q1 and ?q2.0=q2])
        apply (rule safe_postpred_mono[rotated], assumption, blast)
       apply (rule safe_postpred_mono[rotated], assumption, blast)
      apply blast
     apply (metis sepconj_conj_mono)
    apply blast
    done
next
  case (rgsat_iter c r g i p q)
  then show ?case
    using safe_postpred_mono[OF _ safe_iter[of r i n c g]]
    by blast
next
  case (rgsat_atom b r p q g p' q')
  then show ?case
    by (intro safe_atom; blast)
next
  case (rgsat_frame c r g p q f1' f f2')
  then show ?case
    apply (clarsimp simp add: sepconj_conj_def[of p] simp del: sup_apply)
    apply (blast intro: safe_frame)
    done
next
  case (rgsat_disj c r' g' p' q' p q r g)
  then show ?case
    by (metis safe_postpred_mono sup.cobounded2 sup1E sup_ge1)
next
  case (rgsat_conj c r g p1 q1 p2 q2 n hl)
  then show ?case
    by (metis safe_conj inf1E)
next
  case (rgsat_weaken c r' g' p' q' p q r g)
  moreover have \<open>p' (hl, hs)\<close>
    using rgsat_weaken.hyps(3) rgsat_weaken.prems
    by (metis rev_predicate1D)
  ultimately show ?case
    by (meson safe_guarantee_mono safe_postpred_monoD safe_rely_antimonoD)
qed

end
