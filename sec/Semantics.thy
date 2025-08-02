 theory Semantics
  imports "../Soundness"
begin


section \<open> Misc (TODO: move) \<close>

lemma eqrel_times_eqrel_eq[simp]:
  \<open>((=) \<times>\<^sub>R (=)) = (=)\<close>
  by (force simp add: rel_Times_def)

lemma ex_helpers:
  \<open>(\<exists>c1'. (\<exists>c1. P c1 \<and> c1' = f c1) \<and> Q c1') \<longleftrightarrow> (\<exists>c1. P c1 \<and> Q (f c1))\<close>
  by blast

lemma imp_iff_imp_iff:
  \<open>(A \<longrightarrow> B) = (A \<longrightarrow> C) \<longleftrightarrow> (A \<longrightarrow> B = C)\<close>
  by blast

lemma add_leq_Suc0_iff:
  \<open>x + y \<le> Suc 0 \<longleftrightarrow> x \<le> Suc 0 \<and> y = 0 \<or> x = 0 \<and> y \<le> Suc 0\<close>
  by force

lemma sum_leq_Suc0_iff:
  \<open>finite A \<Longrightarrow>
    sum f A \<le> Suc 0 \<longleftrightarrow> (\<forall>x\<in>A. f x = 0) \<or> (\<exists>x\<in>A. f x = Suc 0 \<and> (\<forall>y\<in>A. y \<noteq> x \<longrightarrow> f y = 0))\<close>
  apply (induct rule: finite.induct)
   apply force
  apply (case_tac \<open>a \<in> A\<close>)
   apply (frule mk_disjoint_insert, clarsimp simp add: sum.insert_remove; fail)
  apply (auto simp add: sum.insert_remove conj_disj_distribL le_Suc_eq add_is_1)
  done

lemma iff_extract_agreement:
  \<open>(P \<Longrightarrow> X) \<Longrightarrow> (Q \<Longrightarrow> X) \<Longrightarrow> P = Q \<longleftrightarrow> (X \<longrightarrow> P = Q)\<close>
  by blast


subsection \<open> Sublist \<close>

inductive sublist :: \<open>'a list \<Rightarrow> 'a list \<Rightarrow> bool\<close> (infix \<open>\<preceq>\<^sub>l\<close> 55) where
  sublist_nil[intro!]: \<open>[] \<preceq>\<^sub>l xs\<close>
| sublist_cons[intro!]: \<open>ys' = x # ys \<Longrightarrow> xs \<preceq>\<^sub>l ys \<Longrightarrow> x # xs \<preceq>\<^sub>l ys'\<close>

inductive_cases sublist_nilE[elim!]: \<open>[] \<preceq>\<^sub>l xs\<close>
inductive_cases sublist_consE[elim]: \<open>x # xs \<preceq>\<^sub>l ys'\<close>

lemma sublist_iff[simp]:
  \<open>[] \<preceq>\<^sub>l xs\<close>
  \<open>x # xs \<preceq>\<^sub>l ys' \<longleftrightarrow> (\<exists>ys. ys' = x # ys \<and> xs \<preceq>\<^sub>l ys)\<close>
  by force+

lemma sublist_refl[intro]: \<open>xs \<preceq>\<^sub>l xs\<close>
  by (induct xs) blast+

lemma sublist_trans[trans]: \<open>xs \<preceq>\<^sub>l ys \<Longrightarrow> ys \<preceq>\<^sub>l zs \<Longrightarrow> xs \<preceq>\<^sub>l zs\<close>
  by (induct xs arbitrary: ys zs) force+

lemma sublist_antisym: \<open>xs \<preceq>\<^sub>l ys \<Longrightarrow> ys \<preceq>\<^sub>l xs \<Longrightarrow> xs = ys\<close>
  by (induct xs arbitrary: ys) (force elim: sublist.cases)+

lemma sublist_iff_append:
  \<open>xs \<preceq>\<^sub>l ys \<longleftrightarrow> (\<exists>zs. ys = xs @ zs)\<close>
  by (induct xs arbitrary: ys) force+

lemma ex_list_length_iff_ex_nat:
  \<open>(\<exists>xs. P (length xs)) \<longleftrightarrow> (\<exists>n. P n)\<close>
  by (metis (mono_tags) Ex_list_of_length)


section \<open> RGSep-Security State Types \<close>

type_synonym ('a,'b) rgstate = \<open>(('a \<times> 'a) \<times> ('b \<times> 'b))\<close>

type_synonym ('a,'b) secstate = \<open>(('a \<times> 'b) \<times> ('a \<times> 'b))\<close>


section \<open> Pred-executions \<close>

text \<open>
  Predicate over all states of all executions.
  (N.B. This does not avoid crashes.)
\<close>

type_synonym 's config = \<open>'s \<times> 's comm\<close>

inductive pred_executions
  :: \<open>(('l::pre_perm_alg  \<times> 's) config \<Rightarrow> bool) \<Rightarrow>
      ('l \<times> 's \<Rightarrow> bool) \<Rightarrow>
      ('s \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow>
      ('l \<times> 's) comm \<Rightarrow>
      'l \<times> 's \<Rightarrow>
      nat \<Rightarrow>
      bool\<close>
  where
  pred_executions_nil[intro!, simp]: \<open>pred_executions P F r c s 0\<close>
| pred_executions_step[intro]:
  \<open>\<comment> \<open> The config predicate holds \<close>
    P ((hl, hs), c) \<Longrightarrow>
    \<comment> \<open> rely steps generate states \<close>
    (\<And>hs'. r hs hs' \<Longrightarrow> pred_executions P F r c (hl, hs') n) \<Longrightarrow>
    \<comment> \<open> framed opsteps generate states \<close>
    (\<And>\<alpha> hlhlf' hs' c' hlf.
        hl ## hlf \<Longrightarrow>
        ((hl + hlf, hs), c) \<midarrow>\<alpha>\<rightarrow> ((hlhlf', hs'), c') \<Longrightarrow>
        F (hlf, hs) \<Longrightarrow>
        (\<exists>hl'.
          hl' ## hlf \<and>
          hlhlf' = hl' + hlf \<and>
          (\<alpha> = Tau \<longrightarrow> hl' = hl) \<and>
          pred_executions P F r c' (hl', hs') n)) \<Longrightarrow>
    \<comment> \<open> conclude a step can be made \<close>
    pred_executions P F r c (hl, hs) (Suc n)\<close>

subsection \<open> Proofs about safe \<close>

inductive_cases pred_executions_zeroE[elim!]: \<open>pred_executions P F r c z 0\<close>
inductive_cases pred_executions_sucE[elim]: \<open>pred_executions P F r c z (Suc n)\<close>

lemma pred_executions_suc_iff:
  \<open>pred_executions P F r c z (Suc n) \<longleftrightarrow>
    (\<exists>hl hs. z = (hl, hs) \<and>
      P (z, c) \<and>
      (\<forall>hs'. r hs hs' \<longrightarrow> pred_executions P F r c (hl, hs') n) \<and>
      (\<forall>\<alpha> hlhlf' hs' c' hlf.
          hl ## hlf \<longrightarrow>
          ((hl + hlf,hs), c) \<midarrow>\<alpha>\<rightarrow> ((hlhlf',hs'), c') \<longrightarrow>
          F (hlf, hs) \<longrightarrow>
          (\<exists>hl'.
            hl' ## hlf \<and>
            hlhlf' = hl' + hlf \<and>
            (\<alpha> = Tau \<longrightarrow> hl' = hl) \<and>
            pred_executions P F r c' (hl', hs') n)))\<close>
  apply (rule iffI)
   apply (erule pred_executions_sucE; force)
  apply (case_tac z; force)
  done

lemma pred_executions_pred_mono:
  \<open>p \<le> q \<Longrightarrow> pred_executions p F r c z n \<Longrightarrow> pred_executions q F r c z n\<close>
  apply (induct n arbitrary: c z)
   apply blast
  apply (clarsimp simp add: pred_executions_suc_iff)
  apply (intro conjI, blast, (meson; fail))
  done

lemmas pred_executions_pred_monoD = pred_executions_pred_mono[rotated]


section \<open> Double-state lifting \<close>

subsection \<open> exchange \<close>

definition
  \<open>exch4 \<equiv> \<lambda>((a,b),(c,d)). ((a,c),(b,d))\<close>

lemma exch4_apply[simp]:
  \<open>exch4 ((a,b),(c,d)) = ((a,c),(b,d))\<close>
  by (simp add: exch4_def)

lemma exch4_idem[simp]:
  \<open>exch4 (exch4 x) = x\<close>
  by (simp add: exch4_def split: prod.splits)

lemma comp_exch4_eq_iff[simp]:
  \<open>f \<circ> exch4 = g \<circ> exch4 \<longleftrightarrow> f = g\<close>
  by (simp add: fun_eq_iff, blast)

lemma prod_destruct_exch4_eq[simp]:
  \<open>fst (fst (exch4 x)) = fst (fst x)\<close>
  \<open>fst (snd (exch4 x)) = snd (fst x)\<close>
  \<open>snd (fst (exch4 x)) = fst (snd x)\<close>
  \<open>snd (snd (exch4 x)) = snd (snd x)\<close>
  unfolding exch4_def
  by (clarsimp split: prod.splits)+

lemma prod_part_destruct_exch4_eq[simp]:
  \<open>fst (exch4 (ab, cd)) = (fst ab, fst cd)\<close>
  \<open>snd (exch4 (ab, cd)) = (snd ab, snd cd)\<close>
  by (simp add: exch4_def split: prod.splits)+

lemma le_exch4_shunt:
  \<open>p \<le> q \<circ> exch4 \<longleftrightarrow> p \<circ> exch4 \<le> q\<close>
  by (metis comp_def exch4_idem le_fun_def)

lemma eq_exch4_iff[simp]:
  \<open>((ax, bx), (ay, by)) = exch4 ab \<longleftrightarrow> fst ab = (ax, ay) \<and> snd ab = (bx, by)\<close>
  by (force simp add: exch4_def split: prod.splits)


subsection \<open> relational lifting \<close>

syntax
  "_twoPredLiftBasic"  :: "('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool)"  ("\<lblot> _ \<rblot>" [0] 999)
  "_twoPredLiftDouble"  :: "('a \<Rightarrow> bool) \<Rightarrow> ('b \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> bool)"  ("\<lblot> _ \<bar> _ \<rblot>" [0,0] 998)
  "_twoPredLiftL"  :: "('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> bool)"  ("\<lblot> _ \<bar>" [0] 997)
  "_twoPredLiftR"  :: "('b \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> bool)"  ("\<bar> _ \<rblot>" [0] 997)

translations
  "_twoPredLiftBasic p" \<rightharpoonup> "(CONST pred_Times) p p"
  "_twoPredLiftDouble p q" \<rightleftharpoons> "(CONST pred_Times) p q"
  "_twoPredLiftL p" \<rightharpoonup> "(CONST pred_Times) p \<top>"
  "_twoPredLiftR q" \<rightharpoonup> "(CONST pred_Times) \<top> q"


subsection \<open> Agreement \<close>

definition sec_agree
  :: \<open>('a \<Rightarrow> 'v) \<Rightarrow> 'a \<times> 'a \<Rightarrow> bool\<close> (\<open>\<bbbA>\<close>)
  where
    \<open>\<bbbA> vf \<equiv> (\<lambda>(x,y). vf x = vf y)\<close>

lemma conj_agree_iff:
  \<open>\<bbbA> v1 \<sqinter> \<bbbA> v2 = \<bbbA> (\<lambda>x. (v1 x, v2 x))\<close>
  by (simp add: sec_agree_def exch4_def comp_def fun_eq_iff split: prod.splits)


subsection \<open> Command Times \<close>

function(sequential) comm_Times :: \<open>'a comm \<Rightarrow> 'b comm \<Rightarrow> ('a \<times> 'b) comm\<close> (infixr \<open>\<times>\<^sub>C\<close> 80) where
  \<open>Skip \<times>\<^sub>C Skip = Skip\<close>
| \<open>(cax;;cay) \<times>\<^sub>C (cbx;;cby) = (cax \<times>\<^sub>C cbx) ;; (cay \<times>\<^sub>C cby)\<close>
| \<open>(cax \<parallel> cay) \<times>\<^sub>C (cbx \<parallel> cby) = (cax \<times>\<^sub>C cbx) \<parallel> (cay \<times>\<^sub>C cby)\<close>
| \<open>(cax \<^bold>\<sqinter> cay) \<times>\<^sub>C (cbx \<^bold>\<sqinter> cby) = (cax \<times>\<^sub>C cbx) \<^bold>\<sqinter> (cay \<times>\<^sub>C cby)\<close>
| \<open>(cax \<^bold>\<box> cay) \<times>\<^sub>C (cbx \<^bold>\<box> cby) = (cax \<times>\<^sub>C cbx) \<^bold>\<box> (cay \<times>\<^sub>C cby)\<close>
| \<open>(DO ca OD) \<times>\<^sub>C (DO cb OD) = DO (ca \<times>\<^sub>C cb) OD\<close>
| \<open>\<langle>ra\<rangle> \<times>\<^sub>C \<langle>rb\<rangle> = \<langle>ra \<times>\<^sub>R rb\<rangle>\<close>
| \<open>_ \<times>\<^sub>C _ = undefined\<close>
  by pat_completeness auto (* slow *)

termination
  by (relation \<open>measure (\<lambda>(ca,cb). size ca + size cb)\<close>) simp+


subsection \<open> Double-state Lifting \<close>

(* TODO: move *)
definition diag (\<open>\<Delta>\<close>) where \<open>diag x = (x,x)\<close>
declare diag_def[simp]

abbreviation(input) \<open>liftP p \<equiv> \<lblot> p \<rblot>\<close>
abbreviation(input) \<open>liftR r \<equiv> r \<times>\<^sub>R r\<close>


definition liftC'
  :: \<open>('lx \<times> 'sx) comm \<Rightarrow> ('ly \<times> 'sy) comm \<Rightarrow> (('lx \<times> 'ly) \<times> ('sx \<times> 'sy)) comm\<close>
  where
    \<open>liftC' ca cb \<equiv> map_atom (\<lambda>ar. ar \<circ>\<^sub>2 exch4) (ca \<times>\<^sub>C cb)\<close>

abbreviation liftC :: \<open>('l \<times> 's) comm \<Rightarrow> (('l \<times> 'l) \<times> ('s \<times> 's)) comm\<close> where
  \<open>liftC c \<equiv> liftC' c c\<close>

lemmas liftC_def = liftC'_def

lemma liftC_def':
  \<open>liftC c = map_atom (\<lambda>ar. liftR ar \<circ>\<^sub>2 exch4) c\<close>
  unfolding liftC_def
  by (induct c) simp+

lemmas liftC_simps[simp] =
  map_atom.simps[of \<open>(\<lambda>ar. liftR ar \<circ>\<^sub>2 exch4)\<close>,
    simplified liftC_def'[symmetric]]

lemmas liftC_rev_iff[simp] =
  map_atom_rev_iff[of \<open>(\<lambda>ar. liftR ar \<circ>\<^sub>2 exch4)\<close>,
    simplified liftC_def'[symmetric]]
  map_atom_rev_iff[of \<open>(\<lambda>ar. liftR ar \<circ>\<^sub>2 exch4)\<close>,
    simplified liftC_def'[symmetric], THEN trans[OF eq_commute]]


definition
  \<open>unliftC \<equiv> map_atom (\<lambda>ar. ar \<circ>\<^sub>2 (exch4 \<circ> \<Delta>))\<close>

lemma unliftC_atom_simp:
  \<open>unliftC \<langle>ar\<rangle> = \<langle>\<lambda>x y. ar (exch4 (x, x)) (exch4 (y, y))\<rangle>\<close>
  unfolding unliftC_def
  by force

lemmas unliftC_simp[simp] =
  map_atom.simps(1-5,7)[of \<open>\<lambda>ar. ar \<circ>\<^sub>2 (exch4 \<circ> \<Delta>)\<close>,
    simplified unliftC_def[symmetric]]
  unliftC_atom_simp

lemmas unliftC_rev_iff =
  map_atom_rev_iff[of \<open>\<lambda>ar. ar \<circ>\<^sub>2 (exch4 \<circ> \<Delta>)\<close>,
    simplified unliftC_def[symmetric]]
  map_atom_rev_iff[of \<open>\<lambda>ar. ar \<circ>\<^sub>2 (exch4 \<circ> \<Delta>)\<close>,
    simplified unliftC_def[symmetric], THEN trans[OF eq_commute]]


definition
  \<open>reflclC \<equiv>
  all_atom_comm (\<lambda>ar.
    (\<forall>sx sy sx' sy'.
      ar (exch4 (sx,sx)) (exch4 (sx',sx')) \<and> ar (exch4 (sy,sy)) (exch4 (sy',sy'))
      \<longleftrightarrow> ar (exch4 (sx,sy)) (exch4 (sx',sy'))))\<close>

lemmas reflclC_simp[simp] =
  all_atom_comm_simps[of \<open>(\<lambda>ar.
    (\<forall>sx sy sx' sy'.
      ar (exch4 (sx,sx)) (exch4 (sx',sx')) \<and> ar (exch4 (sy,sy)) (exch4 (sy',sy')) \<longleftrightarrow>
      ar (exch4 (sx,sy)) (exch4 (sx',sy'))))\<close>,
    simplified reflclC_def[symmetric]]


lemma liftC_is_reflcl[simp]:
  \<open>reflclC (liftC c)\<close>
  by (induct c) clarsimp+

lemma unliftC_liftC_cancel[simp]:
  \<open>unliftC (liftC c) = c\<close>
  unfolding unliftC_def liftC_def'
  by (induct c) (simp add: sec_agree_def)+

lemma liftC_unliftC_cancel[simp]:
  \<open>reflclC cc \<Longrightarrow> liftC (unliftC cc) = cc\<close>
  unfolding unliftC_def liftC_def
  by (induct cc) (clarsimp simp add: fun_eq_iff)+


lemma liftC_cancel[simp]:
  \<open>liftC ca = liftC cb \<longleftrightarrow> ca = cb\<close>
  apply (induct cb arbitrary: ca)
        apply (metis liftC_rev_iff(1))
       apply (metis liftC_rev_iff(2))
      apply (metis liftC_rev_iff(3))
     apply (metis liftC_rev_iff(4))
    apply (metis liftC_rev_iff(5))
   apply (fastforce simp add: fun_eq_iff sec_agree_def)
  apply (metis liftC_rev_iff(6))
  done

(*
section \<open> Tree Noninterference \<close>

section \<open> Safe \<close>

abbreviation tree_weak_noninterference where
  \<open>tree_weak_noninterference \<oo> F \<equiv>
    pred_executions
      (\<lambda>((hl,hs),c).
        (\<forall>hlf. F (hlf,hs) \<longrightarrow> hl ## hlf \<longrightarrow> \<bbbA> \<oo> (exch4 (hl + hlf, hs))) \<and>
        (\<exists>cx. c = liftC cx))
      F\<close>

lemma opstep_preserves_liftC:
  \<open>(s, liftC c) \<midarrow>\<alpha>\<rightarrow> (s', cx') \<Longrightarrow> \<exists>c'. cx' = liftC c'\<close>
proof (induct c arbitrary: s s' cx' \<alpha>)
  case Done
  then show ?case by force
next
  case (Seq ca cb)
  then show ?case
    by (cases s, force)
next
  case (Par c1 c2)
  then show ?case
    by (cases s, force)
next
  case (Indet c1 c2)
  then show ?case
    by force
next
  case (Endet ca cb)
  then show ?case
    by (force simp add: Endet.hyps(1,2))
next
  case (Atomic ap aq)
  then show ?case
    by (force split: if_splits)
next
  case (Iter c)
  then show ?case
    by (cases s, force)
qed

theorem weak_noninterference:
  \<open>safe n c s r g q S F \<Longrightarrow>
    c = liftC cx \<Longrightarrow>
    S \<^emph>\<and> F \<le> \<bbbA> \<oo> \<circ> exch4 \<Longrightarrow>
    tree_weak_noninterference \<oo> F r c s n\<close>
  apply (induct arbitrary: s cx rule: safe.inducts)
   apply force
  apply (clarsimp simp add: pred_executions_suc_iff)
  apply (rename_tac c hla hlb hsa hsb)
  apply (intro conjI)
   apply (clarsimp simp add: le_fun_def sepconj_conj_def, blast)
  apply clarsimp
  apply (frule opstep_preserves_liftC)
  apply clarsimp
  apply (drule meta_spec2, drule meta_spec2, drule meta_spec, drule meta_mp,
      rule conjI, assumption, assumption, drule meta_mp, assumption, drule meta_mp, assumption)
  apply blast
  done
*)

(*
    (\<forall>c1 c2. c = c1 \<^bold>\<box> c2 \<or> c = c1 \<^bold>\<sqinter> c2 \<longrightarrow>
      (\<exists>p1 q1 p2 q2.
        (\<exists>c1'. c1 = \<langle> p1, q1 \<rangle> ;; c1') \<and>
        (\<exists>c2'. c2 = \<langle> p2, q2 \<rangle> ;; c2') \<and>
        (\<forall>x y. exch4 (hl, hs) = (x, y) \<longrightarrow>
          \<not> (p1 \<sqinter> pre_state q1 \<sqinter> p2 \<sqinter> pre_state q2) x \<and>
          \<not> (p1 \<sqinter> pre_state q1 \<sqinter> p2 \<sqinter> pre_state q2) y))) \<and>
*)

section \<open> Aligned Traces \<close>

subsection \<open> Parallel-labelled actions \<close>

text \<open> Extended Actions \<close>

datatype aact =
  PL aact |
  PR aact |
  TauINdetL |
  TauINdetR |
  TauBasic | \<comment> \<open> Taus other than Taus from INdet \<close>
  AVis

fun strip_aact :: \<open>aact \<Rightarrow> act\<close> where
  \<open>strip_aact TauBasic = Tau\<close>
| \<open>strip_aact AVis = Vis\<close>
| \<open>strip_aact TauINdetL = Tau\<close>
| \<open>strip_aact TauINdetR = Tau\<close>
| \<open>strip_aact (PL \<alpha>a) = strip_aact \<alpha>a\<close>
| \<open>strip_aact (PR \<alpha>a) = strip_aact \<alpha>a\<close>

fun basic_tau_aact :: \<open>aact \<Rightarrow> bool\<close> where
  \<open>basic_tau_aact TauBasic = True\<close>
| \<open>basic_tau_aact AVis = False\<close>
| \<open>basic_tau_aact TauINdetL = False\<close>
| \<open>basic_tau_aact TauINdetR = False\<close>
| \<open>basic_tau_aact (PL \<alpha>a) = basic_tau_aact \<alpha>a\<close>
| \<open>basic_tau_aact (PR \<alpha>a) = basic_tau_aact \<alpha>a\<close>

text \<open>
  In an aact, a tau move may be buried under parallel synchronisation labels,
  or divided into an INdet Tau, which are handled separately by the evaluation semantics.
  In programs where sub-programs may take actions (\<box>), we need an
  inductive test for whether an action is internal, as the sub-program may be a parallel.
\<close>
definition \<open>tau_aact \<alpha>a \<equiv> strip_aact \<alpha>a = Tau\<close>
definition \<open>vis_aact \<alpha>a \<equiv> strip_aact \<alpha>a = Vis\<close>

lemma not_tau_aact_iff[simp]:
  \<open>\<not> tau_aact \<alpha>a \<longleftrightarrow> vis_aact \<alpha>a\<close>
  by (simp add: tau_aact_def vis_aact_def)

lemma not_vis_aact_iff[simp]:
  \<open>\<not> vis_aact \<alpha>a \<longleftrightarrow> tau_aact \<alpha>a\<close>
  using not_tau_aact_iff by blast

lemma vis_tau_aact_incompatible:
  \<open>vis_aact \<alpha>a \<Longrightarrow> tau_aact \<alpha>a = False\<close>
  \<open>tau_aact \<alpha>a \<Longrightarrow> vis_aact \<alpha>a = False\<close>
  by (simp add: tau_aact_def vis_aact_def)+

lemma vis_aact_unit_def:
  \<open>vis_aact \<alpha>a \<longleftrightarrow> strip_aact \<alpha>a = Vis\<close>
  by (simp add: vis_aact_def)

lemma vis_aact_simps[simp]:
  \<open>vis_aact (PL \<alpha>a) \<longleftrightarrow> vis_aact \<alpha>a\<close>
  \<open>vis_aact (PR \<alpha>a) \<longleftrightarrow> vis_aact \<alpha>a\<close>
  \<open>vis_aact AVis \<longleftrightarrow> True\<close>
  \<open>vis_aact TauBasic \<longleftrightarrow> False\<close>
  \<open>vis_aact TauINdetL \<longleftrightarrow> False\<close>
  \<open>vis_aact TauINdetR \<longleftrightarrow> False\<close>
  by (simp add: vis_aact_def)+

lemma tau_aact_simps[simp]:
  \<open>tau_aact (PL \<alpha>a) \<longleftrightarrow> tau_aact \<alpha>a\<close>
  \<open>tau_aact (PR \<alpha>a) \<longleftrightarrow> tau_aact \<alpha>a\<close>
  \<open>tau_aact AVis \<longleftrightarrow> False\<close>
  \<open>tau_aact TauBasic \<longleftrightarrow> True\<close>
  \<open>tau_aact TauINdetL \<longleftrightarrow> True\<close>
  \<open>tau_aact TauINdetR \<longleftrightarrow> True\<close>
  by (simp add: tau_aact_def)+

lemma all_aact_or_iff[simp]:
  \<open>(\<forall>\<alpha>a. vis_aact \<alpha>a \<or> P \<alpha>a) \<longleftrightarrow> (\<forall>\<alpha>a. tau_aact \<alpha>a \<longrightarrow> P \<alpha>a)\<close>
  \<open>(\<forall>\<alpha>a. tau_aact \<alpha>a \<or> P \<alpha>a) \<longleftrightarrow> (\<forall>\<alpha>a. vis_aact \<alpha>a \<longrightarrow> P \<alpha>a)\<close>
  using not_tau_aact_iff by blast+

lemma basic_tau_aact_then_tau_aact[simp]:
  \<open>basic_tau_aact \<alpha> \<Longrightarrow> tau_aact \<alpha>\<close>
  by (induct \<alpha>) simp+

lemma all_tau_all_vis_iff:
  \<open>(\<forall>\<alpha>. tau_aact \<alpha> \<longrightarrow> P \<alpha>) \<and>
   (\<forall>\<alpha>. vis_aact \<alpha> \<longrightarrow> P \<alpha>) \<longleftrightarrow>
    All P\<close>
  by force


subsection \<open> Parallel Opstep \<close>

text \<open>
  Unfortunately, because acts are often universally quantified,
  using a general type variable becomes prohibitively unwieldy.
  (Due to \<open>itself\<close> types and schematics type vars in \<open>induct\<close>.)
  Thus we just use unit.
\<close>
fun aopstep :: \<open>aact \<Rightarrow> 's pconfig \<Rightarrow> 's pconfig \<Rightarrow> bool\<close> where
  \<open>aopstep \<alpha>a (s, Skip) sc' \<longleftrightarrow> False\<close>
| \<open>aopstep \<alpha>a (s, ca ;; cb) sc' \<longleftrightarrow>
    \<alpha>a = TauBasic \<and> ca = Skip \<and> sc' = (s, cb) \<or>
    (\<exists>s' ca'. aopstep \<alpha>a (s, ca) (s', ca') \<and> sc' = (s', ca' ;; cb))\<close>
| \<open>aopstep \<alpha>a (s, ca \<^bold>\<sqinter> cb) sc' \<longleftrightarrow>
    \<alpha>a = TauINdetL \<and> sc' = (s, ca) \<or>
    \<alpha>a = TauINdetR \<and> sc' = (s, cb)\<close>
| \<open>aopstep \<alpha>a (s, ca \<^bold>\<box> cb) sc' \<longleftrightarrow>
    \<alpha>a = TauBasic \<and> ca = Skip \<and> sc' = (s, cb) \<or>
    \<alpha>a = TauBasic \<and> cb = Skip \<and> sc' = (s, ca) \<or>
    tau_aact \<alpha>a \<and> (\<exists>s' ca'. sc' = (s', ca' \<^bold>\<box> cb) \<and> aopstep \<alpha>a (s, ca) (s', ca')) \<or>
    tau_aact \<alpha>a \<and> (\<exists>s' cb'. sc' = (s', ca \<^bold>\<box> cb') \<and> aopstep \<alpha>a (s, cb) (s', cb')) \<or>
    vis_aact \<alpha>a \<and> aopstep \<alpha>a (s, ca) sc' \<or>
    vis_aact \<alpha>a \<and> aopstep \<alpha>a (s, cb) sc'\<close>
| \<open>aopstep \<alpha>a (s, ca \<parallel> cb) sc' \<longleftrightarrow>
    \<alpha>a = TauBasic \<and> ca = Skip \<and> cb = Skip \<and> sc' = (s, Skip) \<or>
    (\<exists>\<alpha>a'. \<alpha>a = PL \<alpha>a' \<and> (\<exists>s' ca'. aopstep \<alpha>a' (s, ca) (s', ca') \<and> sc' = (s', ca' \<parallel> cb))) \<or>
    (\<exists>\<alpha>a'. \<alpha>a = PR \<alpha>a' \<and> (\<exists>s' cb'. aopstep \<alpha>a' (s, cb) (s', cb') \<and> sc' = (s', ca \<parallel> cb')))\<close>
| \<open>aopstep \<alpha>a (s, DO c OD) sc' \<longleftrightarrow>
    \<alpha>a = TauBasic \<and> (\<forall>\<alpha>a' sc'. \<not> aopstep \<alpha>a' (s, c) sc') \<and> sc' = (s, Skip) \<or>
    (\<exists>s' c'. aopstep \<alpha>a (s, c) (s', c') \<and> sc' = (s', c' ;; DO c OD))\<close>
| \<open>aopstep \<alpha>a (s, \<langle>ar\<rangle>) sc' \<longleftrightarrow>
    (\<alpha>a = AVis \<and> ar s (fst sc') \<and> snd sc' = Skip)\<close>

lemmas aopstep_induct = aopstep.induct[case_names Skip Seq Indet Endet Par DoLoop Atom]


paragraph \<open> Pretty parallel operational semantics \<close>

text \<open> \<open>sc\<close> can step to \<open>sc'\<close> \<close>
abbreviation pretty_aopstep :: \<open>_ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> _\<close> (\<open>_ \<midarrow>(_)\<rightarrow>\<^sub>a _\<close> [60,0,60] 60) where
  \<open>sc \<midarrow>\<alpha>a\<rightarrow>\<^sub>a sc' \<equiv> aopstep \<alpha>a sc sc'\<close>

text \<open> no steps from \<open>sc\<close> can take place \<close>
abbreviation pretty_no_aopstep :: \<open>'s \<times> 's comm \<Rightarrow> bool\<close> (\<open>_ \<midarrow>'/\<rightarrow>\<^sub>a\<close> [60] 60) where
  \<open>sc \<midarrow>/\<rightarrow>\<^sub>a \<equiv> \<forall>\<alpha>a sc'. \<not> aopstep \<alpha>a sc sc'\<close>


subsubsection \<open> aopstep lemmas \<close>

lemma no_aopstep_rgstate_iff:
  \<open>sc \<midarrow>/\<rightarrow>\<^sub>a \<longleftrightarrow> (\<forall>\<alpha> l' s' c'. \<not> aopstep \<alpha> sc ((l', s'), c'))\<close>
  by clarsimp

lemma aopstep_iter_stepD:
  \<open>sc \<midarrow>\<alpha>a\<rightarrow>\<^sub>a sc' \<Longrightarrow>
    sc = (s, c) \<Longrightarrow>
    sc' = (s', c') \<Longrightarrow>
    (s, DO c OD) \<midarrow>\<alpha>a\<rightarrow>\<^sub>a (s', c' ;; DO c OD)\<close>
  by fastforce

lemma aopstep_tau_preserves_state:
  \<open>sc \<midarrow>\<alpha>\<rightarrow>\<^sub>a sc' \<Longrightarrow> tau_aact \<alpha> \<Longrightarrow> fst sc' = fst sc\<close>
  by (induct \<alpha> sc sc' rule: aopstep_induct)
    (fastforce split: if_splits simp add: tau_aact_def)+

lemma vis_aopstep_impl_atom:
  \<open>sc \<midarrow>\<alpha>a\<rightarrow>\<^sub>a sc' \<Longrightarrow>
    vis_aact \<alpha>a \<Longrightarrow>
    \<exists>ar.
      ar \<in># head_atoms (snd sc) \<and>
      ar (fst sc) (fst sc')\<close>
  apply (induct _ sc sc' rule: aopstep_induct; simp add: vis_aact_def tau_aact_def)
      apply fastforce+
  done


lemma vis_aopstep_backwards_endet:
  \<open>sc \<midarrow>\<alpha>a\<rightarrow>\<^sub>a sc' \<Longrightarrow>
    vis_aact \<alpha>a \<Longrightarrow>
    snd sc' = ca' \<^bold>\<box> cb' \<Longrightarrow>
    \<exists>ca cb. snd sc = ca \<^bold>\<box> cb\<close>
  by (induct _ sc sc' arbitrary: ca' cb' rule: aopstep_induct)
    fastforce+

lemma aopstep_then_aopstep_right_seqD:
  \<open>sc \<midarrow>\<alpha>a\<rightarrow>\<^sub>a sc' \<Longrightarrow>
    sc = (s, c) \<Longrightarrow>
    sc' = (s', c') \<Longrightarrow>
    (s, c ;; cx) \<midarrow>\<alpha>a\<rightarrow>\<^sub>a (s', c' ;; cx)\<close>
  by (induct \<alpha>a sc sc' arbitrary: s c s' c' rule: aopstep_induct) simp+

lemma aopstep_then_aopstep_right_endetD:
  \<open>sc \<midarrow>\<alpha>a\<rightarrow>\<^sub>a sc' \<Longrightarrow>
    sc = (s, c) \<Longrightarrow>
    sc' = (s', c') \<Longrightarrow>
    (vis_aact \<alpha>a \<longrightarrow> (s, c \<^bold>\<box> cb) \<midarrow>\<alpha>a\<rightarrow>\<^sub>a (s', c')) \<and>
    (tau_aact \<alpha>a \<longrightarrow> (s, c \<^bold>\<box> cb) \<midarrow>\<alpha>a\<rightarrow>\<^sub>a (s', c' \<^bold>\<box> cb))\<close>
  by (induct \<alpha>a sc sc' arbitrary: s c s' c' rule: aopstep_induct)
    (simp add: vis_aact_def tau_aact_def)+

lemma aopstep_then_aopstep_left_endetD:
  \<open>sc \<midarrow>\<alpha>a\<rightarrow>\<^sub>a sc' \<Longrightarrow>
    sc = (s, c) \<Longrightarrow>
    sc' = (s', c') \<Longrightarrow>
    (vis_aact \<alpha>a \<longrightarrow> (s, ca \<^bold>\<box> c) \<midarrow>\<alpha>a\<rightarrow>\<^sub>a (s', c')) \<and>
    (tau_aact \<alpha>a \<longrightarrow> (s, ca \<^bold>\<box> c) \<midarrow>\<alpha>a\<rightarrow>\<^sub>a (s', ca \<^bold>\<box> c'))\<close>
  by (induct \<alpha>a sc sc' arbitrary: s c s' c' rule: aopstep_induct)
    (simp add: vis_aact_def tau_aact_def)+

lemma aopstep_aact_cases:
  \<open>sc \<midarrow>\<alpha>a\<rightarrow>\<^sub>a sc' \<Longrightarrow>
    (sc \<midarrow>\<alpha>a\<rightarrow>\<^sub>a sc' \<Longrightarrow> vis_aact \<alpha>a \<Longrightarrow> P) \<Longrightarrow>
    (sc \<midarrow>\<alpha>a\<rightarrow>\<^sub>a sc' \<Longrightarrow> tau_aact \<alpha>a \<Longrightarrow> fst sc' = (fst sc) \<Longrightarrow> P) \<Longrightarrow>
    P\<close>
  unfolding vis_aact_def tau_aact_def
  using not_vis_aact_iff aopstep_tau_preserves_state tau_aact_def vis_aact_unit_def by blast

lemma aopstep_no_new_atoms:
  \<open>(s, c) \<midarrow>\<alpha>\<rightarrow>\<^sub>a (ms', c') \<Longrightarrow> set_mset (all_atoms c') \<subseteq> set_mset (all_atoms c)\<close>
  by (induct c arbitrary: \<alpha> c' ms')
    (fastforce split: if_splits)+

lemma aopstep_liftC_then_output_liftC:
  \<open>sscc \<midarrow>\<alpha>\<rightarrow>\<^sub>a msscc' \<Longrightarrow>
    sscc = ((ll, ss), liftC c) \<Longrightarrow>
    msscc' = ((ll', ss'), cc') \<Longrightarrow>
    (\<exists>c'. cc' = liftC c')\<close>
  apply (induct \<alpha> sscc msscc' arbitrary: ll ss c ll' ss' cc' rule: aopstep_induct)
        apply fastforce
       apply clarsimp
       apply (elim disjE; force)
      apply force
     apply clarsimp
     apply (elim disjE; force)
    apply fastforce
   apply fastforce
  apply force
  done


subsubsection \<open> aopstep vs. opstep \<close>

lemma no_opstep_then_no_aopstep:
  \<open>(s, c) \<midarrow>/\<rightarrow> \<Longrightarrow> (s, c) \<midarrow>/\<rightarrow>\<^sub>a\<close>
proof (induct c)
  case (Endet ca cb)
  then show ?case
    by (clarsimp, metis (full_types) ex_act_neq(1))
next
  case (Iter ar)
  then show ?case
    by (clarsimp, metis (full_types) ex_act_neq(1))
qed (clarsimp; blast)+

lemma opstep_then_aopstep:
  \<open>sc \<midarrow>\<alpha>\<rightarrow> sc' \<Longrightarrow> \<exists>\<alpha>'. \<alpha> = strip_aact \<alpha>' \<and> sc \<midarrow>\<alpha>'\<rightarrow>\<^sub>a sc'\<close>
proof (induct \<alpha> sc sc' rule: opstep_induct)
  case (Endet \<alpha> s ca cb sc')
  then show ?case
    by (simp, metis strip_aact.simps(1) tau_aact_def vis_aact_def)
next
  case (Par \<alpha> s ca cb sc')
  then show ?case
    by (simp, metis strip_aact.simps(1,5,6))
next
  case (DoLoop \<alpha> s c sc')
  then show ?case
    using no_opstep_then_no_aopstep[of s c]
    by force
qed force+

lemma no_aopstep_then_no_opstep:
  \<open>(s, c) \<midarrow>/\<rightarrow>\<^sub>a \<Longrightarrow> (s, c) \<midarrow>/\<rightarrow>\<close>
  by (meson opstep_then_aopstep)

lemma aopstep_then_opstep:
  \<open>sc \<midarrow>\<alpha>\<rightarrow>\<^sub>a sc' \<Longrightarrow> sc \<midarrow>strip_aact \<alpha>\<rightarrow> sc'\<close>
proof (induct rule: aopstep_induct)
  case (Endet \<alpha>a s ca cb sc')
  then show ?case
    by (clarsimp, metis (full_types) act_not_eq_iff(1) strip_aact.simps(1)
        vis_aact_def tau_aact_def)
next
  case (DoLoop \<alpha>a s c sc')
  then show ?case
    using opstep_then_aopstep
    by (clarsimp, metis strip_aact.simps(1))
qed force+


subsubsection \<open> Self-aopstep Impossible \<close>

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

fun eval_focus :: \<open>'a comm \<Rightarrow> 'a comm set\<close> where
  \<open>eval_focus Skip = {Skip}\<close>
| \<open>eval_focus (ca ;; cb) = (if ca = Skip then {ca ;; cb} else eval_focus ca)\<close>
| \<open>eval_focus (ca \<parallel> cb) = (eval_focus ca \<union> eval_focus cb)\<close>
| \<open>eval_focus (ca \<^bold>\<sqinter> cb) = {ca \<^bold>\<sqinter> cb}\<close>
| \<open>eval_focus (ca \<^bold>\<box> cb) = eval_focus ca \<union> eval_focus cb\<close>
| \<open>eval_focus \<langle>ar\<rangle> = {\<langle>ar\<rangle>}\<close>
| \<open>eval_focus (DO c OD) = {c, DO c OD}\<close>

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

lemma self_aopstep_endet_cluster_then_crash:
  \<open>endet_expansion c c' \<Longrightarrow> (s, c) \<midarrow>\<alpha>a\<rightarrow>\<^sub>a (s', c') \<Longrightarrow> False\<close>
proof (induct c arbitrary: \<alpha>a c')
  case (Endet c1 c2)
  then show ?case
    by (clarsimp, metis comm.inject(4) eexp_reflI endet_expansion_right_EndetE
        endet_expansion_endet_leftD(1,2) endet_expansion_indet_left(7,8))
qed force+

lemmas self_aopstep_endet_cluster_then_crashD = 
  self_aopstep_endet_cluster_then_crash[rotated]

lemma self_aopstep_impossible[simp]:
  \<open>(s, c) \<midarrow>\<alpha>a\<rightarrow>\<^sub>a (s', c) = False\<close>
  \<open>(s, c1) \<midarrow>\<alpha>a\<rightarrow>\<^sub>a (s', c1 \<^bold>\<box> c2) = False\<close>
  \<open>(s, c2) \<midarrow>\<alpha>a\<rightarrow>\<^sub>a (s', c1 \<^bold>\<box> c2) = False\<close>
  by (force dest: self_aopstep_endet_cluster_then_crashD)+

lemma aopstep_endet_skip_then:
  \<open>(s, c \<^bold>\<box> Skip) \<midarrow>\<alpha>a\<rightarrow>\<^sub>a (s', c) \<Longrightarrow> tau_aact \<alpha>a \<and> s' = s\<close>
  \<open>(s, Skip \<^bold>\<box> c) \<midarrow>\<alpha>a\<rightarrow>\<^sub>a (s', c) \<Longrightarrow> tau_aact \<alpha>a \<and> s' = s\<close>
  by (clarsimp, metis aopstep_tau_preserves_state fst_conv tau_aact_simps(4))+


subsection \<open> parallel-annotated opsteps \<close>

inductive aopsteps
  :: \<open>_ list \<Rightarrow>
      ('l \<times> 's) \<times> ('l \<times> 's) comm \<Rightarrow>
      ('l \<times> 's) \<times> ('l \<times> 's) comm \<Rightarrow>
      bool\<close>
  where
  aopsteps_nil[intro!]:
  \<open>sc' = sc \<Longrightarrow> aopsteps [] sc sc'\<close>
| aopsteps_step[intro]:
  \<open>aopstep \<alpha> sc sc' \<Longrightarrow>
    aopsteps \<rho> sc' sc'' \<Longrightarrow>
    aopsteps (\<alpha> # \<rho>) sc sc''\<close>

inductive_cases aopsteps_nilE[elim!]: \<open>aopsteps [] sc sc'\<close>
inductive_cases aopsteps_consE[elim]: \<open>aopsteps (\<alpha> # \<rho>) sc sc'\<close>

lemmas aopsteps_induct = aopsteps.induct[case_names nil crash step]

abbreviation aopsteps_pretty :: \<open>_ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> bool\<close> (\<open>_ \<midarrow>_\<rightarrow>\<^sub>a\<^sup>* _\<close> [50, 0, 50]) where
  \<open>sc \<midarrow>\<rho>a\<rightarrow>\<^sub>a\<^sup>* sc' \<equiv> aopsteps \<rho>a sc sc'\<close>

lemma aopsteps_simps[simp]:
  \<open>aopsteps [] sc sc' \<longleftrightarrow> sc' = sc\<close>
  \<open>aopsteps (\<alpha> # \<rho>) sc sc'' \<longleftrightarrow> (\<exists>sc'. aopstep \<alpha> sc sc' \<and> aopsteps \<rho> sc' sc'')\<close>
  by blast+


subsubsection \<open> Lemmas \<close>

lemma aopsteps_tau_preserves_state:
  \<open>sc \<midarrow>\<rho>\<rightarrow>\<^sub>a\<^sup>* sc' \<Longrightarrow> list_all tau_aact \<rho> \<Longrightarrow> fst sc' = fst sc\<close>
  by (induct rule: aopsteps.induct)
    (fastforce split: if_splits simp add: tau_aact_def dest: aopstep_tau_preserves_state)+

lemma aopsteps_rcons:
  \<open>sc \<midarrow>\<rho>\<rightarrow>\<^sub>a\<^sup>* sc' \<Longrightarrow>
    sc' \<midarrow>\<alpha>\<rightarrow>\<^sub>a sc'' \<Longrightarrow>
    sc \<midarrow>\<rho> @ [\<alpha>]\<rightarrow>\<^sub>a\<^sup>* sc''\<close>
  by (induct arbitrary: sc'' rule: aopsteps.induct)
   fastforce+

lemma aopsteps_iff:
  \<open>sc \<midarrow>\<rho>\<rightarrow>\<^sub>a\<^sup>* sc'' \<longleftrightarrow>
    \<rho> = [] \<and> sc'' = sc \<or>
    (\<exists>\<alpha> \<rho>'. \<rho> = \<alpha> # \<rho>' \<and> (\<exists>sc'. sc \<midarrow>\<alpha>\<rightarrow>\<^sub>a sc' \<and> sc' \<midarrow>\<rho>'\<rightarrow>\<^sub>a\<^sup>* sc''))\<close>
  by (induct \<rho>) force+


subsubsection \<open> Reverse Aopsteps \<close>

inductive aopsteps_rev
  :: \<open>_ list \<Rightarrow>
      ('l \<times> 's) \<times> ('l \<times> 's) comm \<Rightarrow>
      ('l \<times> 's) \<times> ('l \<times> 's) comm \<Rightarrow>
      bool\<close>
  where
  aopsteps_rev_nil[intro!]:
  \<open>sc'' = sc \<Longrightarrow> aopsteps_rev [] sc sc''\<close>
| aopsteps_rev_cons[intro!]:
  \<open>aopsteps_rev \<rho> sc sc' \<Longrightarrow>
    aopstep \<alpha> sc' sc'' \<Longrightarrow>
    aopsteps_rev (\<rho> @ [\<alpha>]) sc sc''\<close>

lemmas aopsteps_rev_singletonI[intro!] = aopsteps_rev_cons[of \<open>[]\<close>, OF aopsteps_rev_nil, simplified]

inductive_cases aopsteps_rev_nilE[elim!]: \<open>aopsteps_rev [] sc sc'\<close>
inductive_cases aopsteps_rev_rconsE[elim!]: \<open>aopsteps_rev (\<rho>e @ [\<alpha>e]) sc sc'\<close>

abbreviation aopsteps_rev_pretty :: \<open>_ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> bool\<close> (\<open>_ \<midarrow>_\<rightarrow>\<^sub>a\<^sub>r\<^sup>* _\<close> [50, 0, 50]) where
  \<open>sc \<midarrow>\<rho>e\<rightarrow>\<^sub>a\<^sub>r\<^sup>* sc' \<equiv> aopsteps_rev \<rho>e sc sc'\<close>

lemma aopsteps_rev_simps[simp]:
  \<open>aopsteps_rev [] sc sc' \<longleftrightarrow> sc' = sc\<close>
  \<open>aopsteps_rev (\<rho>e @ [\<alpha>e]) sc sc'' \<longleftrightarrow>
    (\<exists>sc'. aopsteps_rev \<rho>e sc sc' \<and> aopstep \<alpha>e sc' sc'')\<close>
  by force+

paragraph \<open> Aopsteps-rev to Aopsteps \<close>

lemma aopsteps_rev_aopsteps_to_aopsteps:
  \<open>aopsteps_rev \<rho>x sc sc' \<Longrightarrow>
    aopsteps \<rho>y sc' sc'' \<Longrightarrow>
    aopsteps (\<rho>x @ \<rho>y) sc sc''\<close>
  apply (induct arbitrary: \<rho>y sc'' rule: aopsteps_rev.induct)
   apply force
  apply (clarsimp, blast)
  done

lemma aopsteps_rev_to_aopsteps:
  \<open>aopsteps_rev \<rho> sc sc' \<Longrightarrow> aopsteps \<rho> sc sc'\<close>
  using aopsteps_rev_aopsteps_to_aopsteps[where \<rho>y=\<open>[]\<close> and sc'=sc' and sc''=sc', simplified]
  by (case_tac sc', simp)

paragraph \<open> Aopsteps to Aopsteps-rev \<close>

lemma aopsteps_rev_aopsteps_to_aopsteps_rev:
  \<open>aopsteps \<rho>y sc' sc'' \<Longrightarrow>
    aopsteps_rev \<rho>x sc sc' \<Longrightarrow>
    aopsteps_rev (\<rho>x @ \<rho>y) sc sc''\<close>
  by (induct arbitrary: \<rho>x rule: aopsteps.induct) force+

lemma aopsteps_to_aopsteps_rev:
  \<open>aopsteps \<rho> sc sc' \<Longrightarrow> aopsteps_rev \<rho> sc sc'\<close>
  using aopsteps_rev_aopsteps_to_aopsteps_rev[where \<rho>x=\<open>[]\<close> and sc=sc and sc''=sc', simplified]
  by auto


section \<open> Extended step \<close>

datatype 'a eact =
  Env
  | Loc \<open>'a\<close>

lemma map_eact_rev[simp]:
  \<open>map_eact f \<alpha>e = Env \<longleftrightarrow> \<alpha>e = Env\<close>
  \<open>map_eact f \<alpha>e = Loc \<alpha> \<longleftrightarrow> (\<exists>\<alpha>'. \<alpha>e = Loc \<alpha>' \<and> \<alpha> = f \<alpha>')\<close>
  by (cases \<alpha>e; force)+

lemmas map_eact_rev'[simp] = map_eact_rev[THEN trans[rotated], OF eq_commute]


definition
  \<open>estep step R F \<equiv>
    \<lambda>\<alpha>e. case \<alpha>e of
      Env \<Rightarrow>
        (\<lambda>sc sc'.
          snd sc' = snd sc \<and>
          fst (fst sc') = fst (fst sc) \<and>
          R (snd (fst sc)) (snd (fst sc')) \<and>
          (\<exists>f. F (f, snd (fst sc)) \<and> fst (fst sc) ## f) \<and>
          (\<exists>f. F (f, snd (fst sc')) \<and> fst (fst sc') ## f))
      | Loc \<alpha> \<Rightarrow>
        (\<lambda>((sl, ss), c) ((sl', ss'), c').
          \<exists>f.
            F (f, ss) \<and>
            sl ## f \<and>
            F (f, ss') \<and>
            sl' ## f \<and>
            step \<alpha> ((sl + f, ss), c) ((sl' + f, ss'), c'))\<close>


paragraph \<open> Pretty extended extended opsem \<close>

abbreviation pretty_estep :: \<open>_ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> bool\<close> (\<open>_ \<midarrow>_, _, _\<rightarrow>\<^sub>e _\<close> [60,0,0,0,60] 60) where
  \<open>sc \<midarrow>r, F, \<gamma>\<rightarrow>\<^sub>e sc' \<equiv> estep opstep r F \<gamma> sc sc'\<close>

abbreviation pretty_no_estep :: \<open>_ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> bool\<close> (\<open>_ \<midarrow>_, _ '/\<rightarrow>\<^sub>e\<close> [60, 0, 0] 60) where
  \<open>sc \<midarrow>r, F /\<rightarrow>\<^sub>e \<equiv> \<forall>\<gamma>. \<forall>sc'::_\<times>_. \<not> estep opstep r F \<gamma> sc sc'\<close>

abbreviation pretty_eastep :: \<open>_ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> bool\<close> (\<open>_ \<midarrow>_, _, _\<rightarrow>\<^sub>e\<^sub>a _\<close> [60,0,0,0,60] 60) where
  \<open>sc \<midarrow>r, F, \<gamma>\<rightarrow>\<^sub>e\<^sub>a sc' \<equiv> estep aopstep r F \<gamma> sc sc'\<close>

abbreviation prsetty_no_eastep :: \<open>_ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> bool\<close> (\<open>_ \<midarrow>_, _ '/\<rightarrow>\<^sub>e\<^sub>a\<close> [60, 0, 0] 60) where
  \<open>sc \<midarrow>r, F /\<rightarrow>\<^sub>e\<^sub>a \<equiv> \<forall>\<gamma>. \<forall>sc'::_\<times>_. \<not> estep aopstep r F \<gamma> sc sc'\<close>


subsection \<open> Lemmas about estep \<close>

lemma estep_simps[simp]:
  \<open>estep step R F Env sc sc' =
    (snd sc' = snd sc \<and>
      fst (fst sc') = fst (fst sc) \<and>
      R (snd (fst sc)) (snd (fst sc')) \<and>
      (\<exists>f. F (f, snd (fst sc)) \<and> fst (fst sc) ## f) \<and>
      (\<exists>f. F (f, snd (fst sc')) \<and> fst (fst sc) ## f))\<close>
  \<open>estep step R F (Loc \<alpha>) sc sc' =
    (\<exists>f.
      F (f, snd (fst sc)) \<and>
      fst (fst sc) ## f \<and>
      F (f, snd (fst sc')) \<and>
      fst (fst sc') ## f \<and>
      step \<alpha>
        ((fst (fst sc) + f, snd (fst sc)), snd sc)
        ((fst (fst sc') + f, snd (fst sc')), snd sc'))\<close>
  by (force simp add: estep_def split: sum.splits unit.splits prod.splits)+

lemma estepE[elim]:
  \<open>estep step R F \<alpha>e sc sc' \<Longrightarrow>
    (\<And>xl xs c xs' xf xf'.
      \<alpha>e = Env \<Longrightarrow>
      sc = ((xl, xs), c) \<Longrightarrow>
      sc' = ((xl, xs'), c) \<Longrightarrow>
      R xs xs' \<Longrightarrow>
      F (xf, xs) \<Longrightarrow>
      xl ## xf \<Longrightarrow>
      F (xf', xs') \<Longrightarrow>
      xl ## xf' \<Longrightarrow>
      P) \<Longrightarrow>
    (\<And>\<alpha> xl xs c mx' c' xf mxf'.
      \<alpha>e = Loc \<alpha> \<Longrightarrow>
      sc = ((xl,xs),c) \<Longrightarrow>
      sc' = (mx',c') \<Longrightarrow>
      F (xf, xs) \<Longrightarrow>
      xl ## xf \<Longrightarrow>
      step \<alpha> ((xl + xf,xs),c) (mxf', c') \<and>
      (\<exists>xl' xlf' xs'.
        mxf' = (xlf', xs') \<and>
        F (xf, xs') \<and>
        xl' ## xf \<and>
        xlf' = xl' + xf \<and>
        mx' = (xl', xs')) \<Longrightarrow>
      P) \<Longrightarrow>
    P\<close>
  by (cases sc, cases sc', cases \<alpha>e; force)

lemma estep_def':
  \<open>estep step R F \<alpha>e sc sc' \<longleftrightarrow>
    \<alpha>e = Env \<and>
    (snd sc' = snd sc \<and>
      fst (fst sc') = fst (fst sc) \<and>
      R (snd (fst sc)) (snd (fst sc')) \<and>
      (\<exists>f. F (f, snd (fst sc)) \<and> fst (fst sc) ## f) \<and>
      (\<exists>f. F (f, snd (fst sc')) \<and> fst (fst sc) ## f)) \<or>
    (\<exists>\<alpha>. \<alpha>e = Loc \<alpha> \<and> (\<exists>f.
      F (f, snd (fst sc)) \<and>
      fst (fst sc) ## f \<and>
      F (f, snd (fst sc')) \<and>
      fst (fst sc') ## f \<and>
      step \<alpha>
        ((fst (fst sc) + f, snd (fst sc)), snd sc)
        ((fst (fst sc') + f, snd (fst sc')), snd sc')))\<close>
  by (cases \<alpha>e; simp)

lemma estep_skip_iff[simp]:
  \<open>\<forall>\<alpha> s sc'. \<not> step \<alpha> (s, Skip) sc' \<Longrightarrow>
    estep step R F \<alpha>e (s, Skip) sc' \<longleftrightarrow>
      \<alpha>e = Env \<and>
      snd sc' = Skip \<and>
      fst (fst sc') = fst s \<and>
      R (snd s) (snd (fst sc')) \<and>
      (\<exists>f. F (f, snd s) \<and> fst s ## f) \<and>
      (\<exists>f. F (f, snd (fst sc')) \<and> fst (fst sc') ## f)\<close>
  unfolding estep_def
  by (cases \<alpha>e; clarsimp split: prod.splits)


subsubsection \<open> Eastep Complex Lemmas \<close>

lemma eastep_then_eastep_right_par:
  \<open>(s, c) \<midarrow>r, F, \<alpha>e\<rightarrow>\<^sub>e\<^sub>a (s', c') \<Longrightarrow>
    (s, c \<parallel> cb) \<midarrow>r, F, map_eact PL \<alpha>e\<rightarrow>\<^sub>e\<^sub>a (s', c' \<parallel> cb)\<close>
  unfolding estep_def
  by (force split: prod.splits eact.splits)

lemma eastep_then_eastep_left_par:
  \<open>(s, c) \<midarrow>r, F, \<gamma>\<rightarrow>\<^sub>e\<^sub>a (s', c') \<Longrightarrow>
    (s, ca \<parallel> c) \<midarrow>r, F, map_eact PR \<gamma>\<rightarrow>\<^sub>e\<^sub>a (s', ca \<parallel> c')\<close>
  unfolding estep_def
  by (force split: prod.splits eact.splits)

lemma eastep_then_eastep_right_endet:
  \<open>(s, c) \<midarrow>r, F, \<gamma>\<rightarrow>\<^sub>e\<^sub>a (s', c') \<Longrightarrow>
    (\<forall>\<alpha>a. \<gamma> = Env \<longrightarrow> (s, c \<^bold>\<box> cb) \<midarrow>r, F, \<gamma>\<rightarrow>\<^sub>e\<^sub>a (s', c' \<^bold>\<box> cb)) \<and>
    (\<forall>\<alpha>a. \<gamma> = Loc \<alpha>a \<longrightarrow>
      (vis_aact \<alpha>a \<longrightarrow> (s, c \<^bold>\<box> cb) \<midarrow>r, F, \<gamma>\<rightarrow>\<^sub>e\<^sub>a (s', c')) \<and>
      (tau_aact \<alpha>a \<longrightarrow> (s, c \<^bold>\<box> cb) \<midarrow>r, F, \<gamma>\<rightarrow>\<^sub>e\<^sub>a (s', c' \<^bold>\<box> cb)))\<close>
  unfolding estep_def
  by (force split: prod.splits simp add: vis_aact_def tau_aact_def)

lemma eastep_then_eastep_left_endet:
  \<open>(s, c) \<midarrow>r, F, \<gamma>\<rightarrow>\<^sub>e\<^sub>a (s', c') \<Longrightarrow>
    (\<forall>\<alpha>a. \<gamma> = Env \<longrightarrow> (s, ca \<^bold>\<box> c) \<midarrow>r, F, \<gamma>\<rightarrow>\<^sub>e\<^sub>a (s', ca \<^bold>\<box> c')) \<and>
    (\<forall>\<alpha>a. \<gamma> = Loc \<alpha>a \<longrightarrow>
      (vis_aact \<alpha>a \<longrightarrow> (s, ca \<^bold>\<box> c) \<midarrow>r, F, \<gamma>\<rightarrow>\<^sub>e\<^sub>a (s', c')) \<and>
      (tau_aact \<alpha>a \<longrightarrow> (s, ca \<^bold>\<box> c) \<midarrow>r, F, \<gamma>\<rightarrow>\<^sub>e\<^sub>a (s', ca \<^bold>\<box> c')))\<close>
  unfolding estep_def
  by (force split: prod.splits simp add: vis_aact_def tau_aact_def)

lemma estep_then_estep_doloop:
  \<open>(s, c) \<midarrow>r, F, \<gamma>\<rightarrow>\<^sub>e\<^sub>a (s', c') \<Longrightarrow>
    (\<forall>\<alpha>a. \<gamma> = Env \<longrightarrow> (s, DO c OD) \<midarrow>r, F, \<gamma>\<rightarrow>\<^sub>e\<^sub>a (s', DO c' OD)) \<and>
    (\<forall>\<alpha>a. \<gamma> = Loc \<alpha>a \<longrightarrow> (s, DO c OD) \<midarrow>r, F, \<gamma>\<rightarrow>\<^sub>e\<^sub>a (s', c' ;; DO c OD))\<close>
  unfolding estep_def
  by (force split: prod.splits)


lemma aopstep_preserves_reflclC:
  \<open>sscc \<midarrow>\<rho>\<rightarrow>\<^sub>a msscc' \<Longrightarrow>
    reflclC (snd sscc) \<Longrightarrow>
    reflclC (snd msscc')\<close>
  by (induct rule: aopstep_induct)
    (fastforce simp add: if_bool_eq_disj)+

lemma eaopstep_preserves_reflclC:
  \<open>sscc \<midarrow>RR, FF, \<rho>\<rightarrow>\<^sub>e\<^sub>a msscc' \<Longrightarrow>
    reflclC (snd sscc) \<Longrightarrow>
    reflclC (snd msscc')\<close>
  apply (erule estepE)
   apply force
  apply (metis aopstep_preserves_reflclC snd_conv)
  done


subsection \<open> Extended steps \<close>

inductive esteps :: \<open>_ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> bool\<close> for step where
  esteps_nil[intro!]:
  \<open>sc' = sc \<Longrightarrow> esteps step r F [] sc sc'\<close>
| esteps_step[intro!]:
  \<open>estep step r F \<alpha> sc sc' \<Longrightarrow>
    esteps step r F \<rho> sc' sc'' \<Longrightarrow>
    esteps step r F (\<alpha> # \<rho>) sc sc''\<close>

inductive_cases esteps_nilE[elim!]: \<open>esteps step r F [] sc sc'\<close>
inductive_cases esteps_consE[elim!]: \<open>esteps step r F (\<alpha> # \<rho>) sc sc'\<close>

abbreviation esteps_pretty :: \<open>_ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> bool\<close>
  (\<open>_ \<midarrow>_, _, _\<rightarrow>\<^sub>e\<^sup>* _\<close> [55, 0, 0, 0, 55])
  where
    \<open>sc \<midarrow>r, F, \<gamma>s\<rightarrow>\<^sub>e\<^sup>* sc' \<equiv> esteps opstep r F \<gamma>s sc sc'\<close>

lemmas esteps_induct = esteps.induct[of opstep, consumes 1]

abbreviation easteps_pretty :: \<open>_ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> bool\<close>
  (\<open>_ \<midarrow>_, _, _\<rightarrow>\<^sub>e\<^sub>a\<^sup>* _\<close> [55, 0, 0, 0, 55])
  where
    \<open>sc \<midarrow>r, F, \<gamma>s\<rightarrow>\<^sub>e\<^sub>a\<^sup>* sc' \<equiv> esteps aopstep r F \<gamma>s sc sc'\<close>

lemmas easteps_induct = esteps.induct[of aopstep, consumes 1]

lemma easteps_iff[simp]:
  \<open>esteps step R F [] sc sc' \<longleftrightarrow> sc' = sc\<close>
  \<open>esteps step R F (\<alpha> # \<rho>) sc sc'' \<longleftrightarrow>
    (\<exists>sc'. estep step R F \<alpha> sc sc' \<and> esteps step R F \<rho> sc' sc'')\<close>
   by force+


subsection \<open> Reverse Extended Steps \<close>

inductive esteps_rev :: \<open>_ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> bool\<close> for step r F where
  esteps_rev_nil[intro!]:
  \<open>sc' = sc \<Longrightarrow> esteps_rev step r F [] sc sc'\<close>
| esteps_rev_rcons[intro!]: \<open>
  esteps_rev step r F \<rho> sc sc' \<Longrightarrow>
  estep step r F \<alpha> sc' sc'' \<Longrightarrow>
  esteps_rev step r F (\<rho> @ [\<alpha>]) sc sc''\<close>

inductive_cases esteps_rev_nilE[elim!]: \<open>esteps_rev step r F [] sc sc'\<close>
inductive_cases esteps_rev_consE[elim]: \<open>esteps_rev step r F (\<rho> @ [\<alpha>]) sc sc'\<close>

lemmas esteps_rev_singleton[intro!] =
  esteps_rev_rcons[of _ _ _ \<open>[]\<close>, OF esteps_rev_nil, simplified]


abbreviation esteps_rev_pretty :: \<open>_ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> bool\<close>
  (\<open>_ \<midarrow>_, _, _\<rightarrow>\<^sub>e\<^sub>r\<^sup>* _\<close> [55, 0, 0, 0, 55])
  where
    \<open>sc \<midarrow>R, F, \<rho>\<rightarrow>\<^sub>e\<^sub>r\<^sup>* sc' \<equiv> esteps_rev opstep R F \<rho> sc sc'\<close>

lemmas esteps_rev_induct = esteps_rev.induct[of opstep, consumes 1, case_names Nil Rcons]

abbreviation easteps_rev_pretty :: \<open>_ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> bool\<close>
  (\<open>_ \<midarrow>_, _, _\<rightarrow>\<^sub>e\<^sub>a\<^sub>r\<^sup>* _\<close> [55, 0, 0, 0, 55])
  where
    \<open>sc \<midarrow>R, F, \<rho>\<rightarrow>\<^sub>e\<^sub>a\<^sub>r\<^sup>* sc' \<equiv> esteps_rev aopstep R F \<rho> sc sc'\<close>

lemmas easteps_rev_induct = esteps_rev.induct[of aopstep, consumes 1, case_names Nil Rcons]

lemma easteps_rev_iff[simp]:
  \<open>esteps_rev step R F [] sc sc' \<longleftrightarrow> sc' = sc\<close>
  \<open>esteps_rev step R F (\<rho> @ [\<alpha>]) sc sc'' \<longleftrightarrow>
    (\<exists>sc'. esteps_rev step R F \<rho> sc sc' \<and> estep step R F \<alpha> sc' sc'')\<close>
  by force+

paragraph \<open> Esteps-rev to Esteps \<close>

lemma esteps_rev_esteps_to_esteps:
  \<open>esteps_rev step R F \<rho>x sc sc' \<Longrightarrow>
    esteps step R F \<rho>y sc' sc'' \<Longrightarrow>
    esteps step R F (\<rho>x @ \<rho>y) sc sc''\<close>
  by (induct arbitrary: \<rho>y sc'' rule: esteps_rev.induct) force+

lemma esteps_rev_to_esteps:
  \<open>esteps_rev step R F \<rho> sc sc' \<Longrightarrow> esteps step R F \<rho> sc sc'\<close>
  using esteps_rev_esteps_to_esteps[where \<rho>y=\<open>[]\<close> and sc'=sc' and sc''=sc', of step R F]
  by (case_tac sc', simp)

paragraph \<open> Esteps to Esteps-rev \<close>

lemma esteps_rev_esteps_to_esteps_rev:
  \<open>esteps step R F \<rho>y sc' sc'' \<Longrightarrow>
    esteps_rev step R F \<rho>x sc sc' \<Longrightarrow>
    esteps_rev step R F (\<rho>x @ \<rho>y) sc sc''\<close>
  by (induct arbitrary: \<rho>x rule: esteps.induct) force+

lemma esteps_to_esteps_rev:
  \<open>esteps step R F \<rho> sc sc' \<Longrightarrow> esteps_rev step R F \<rho> sc sc'\<close>
  using esteps_rev_esteps_to_esteps_rev[where \<rho>x=\<open>[]\<close> and sc=sc and sc''=sc', of step R F, simplified]
  by auto


(*
section \<open> Double Step \<close>

inductive dstep
  :: \<open>('s \<times> 's \<Rightarrow> 's \<times> 's \<Rightarrow> bool) \<Rightarrow>
        (('l::pre_perm_alg \<times> 'l) \<times> ('s \<times> 's) \<Rightarrow> bool) \<Rightarrow>
      (('l \<times> 's) comm \<Rightarrow> ('l \<times> 's) comm \<Rightarrow> bool) \<Rightarrow>
      _ eact list \<times> _ eact list \<Rightarrow>
      (('l \<times> 's) \<times> ('l \<times> 's) comm) \<times> (('l \<times> 's) \<times> ('l \<times> 's) comm) \<Rightarrow>
      (('l \<times> 's + unit) \<times> ('l \<times> 's) comm) \<times> (('l \<times> 's + unit) \<times> ('l \<times> 's) comm) \<Rightarrow>
      bool\<close>
  where
  dstep_env[intro!]:
    \<open>RR (sx,sy) (sx',sy') \<Longrightarrow>
      CC cx cy \<Longrightarrow>
      dstep RR FF CC ([Env], [Env])
        (((lx,sx),cx), ((ly,sy),cy))
        (((lx, sx'),cx), ((ly,sy'),cy))\<close>
| dstep_tau_left[intro]:
  \<open>FF ((fx,fy),(snd sx, snd sy)) \<Longrightarrow>
    CC cx cy \<Longrightarrow>
    \<comment> \<open> left step \<close>
    fst sx ## fx \<Longrightarrow>
    aopstep \<alpha>x ((fst sx + fx, snd sx),cx) ((fst sx' + fx, snd sx'),cx') \<Longrightarrow>
    basic_tau_aact \<alpha>x \<Longrightarrow>
    dstep RR FF CC ([Loc \<alpha>x], [])
      ((sx,cx), (sy,cy))
      ((sx', cx'), (sy, cy))\<close>
| dstep_tau_right[intro]:
  \<open>FF ((fx,fy),(snd sx, snd sy)) \<Longrightarrow>
    CC cx cy \<Longrightarrow>
    \<comment> \<open> right step \<close>
    fst sx ## fx \<Longrightarrow>
    aopstep \<alpha>y ((fst sy + fy, snd sy), cy) ((fst sy' + fy, snd sy'), cy') \<Longrightarrow>
    basic_tau_aact \<alpha>y \<Longrightarrow>
    dstep RR FF CC ([], [Loc \<alpha>y])
      ((sx,cx), (sy,cy))
      ((sx, cx), (sy', cy'))\<close>
| dstep_local[intro]:
  \<open>FF ((fx,fy),(snd sx, snd sy)) \<Longrightarrow>
    CC cx cy \<Longrightarrow>
    \<comment> \<open> left steps \<close>
    fst sx ## fx \<Longrightarrow>
    aopstep \<alpha> ((fst sx + fx, snd sx), cx) ((fst sx' + fx, snd sx'), cx') \<Longrightarrow>
    \<comment> \<open> right steps \<close>
    fst sy ## fy \<Longrightarrow>
    aopstep \<alpha> ((fst sy + fy, snd sy), cy) ((fst sy' + fy, snd sy'), cy') \<Longrightarrow>
    dstep RR FF CC ([Loc \<alpha>], [Loc \<alpha>])
      ((sx,cx), (sy,cy))
      ((sx', cx'), (sy', cy'))\<close>

inductive_cases dstep_nilLE[elim!]: \<open>dstep RR FF CC ([], Y) ss zz'\<close>
inductive_cases dstep_nilRE[elim!]: \<open>dstep RR FF CC (X, []) ss zz'\<close>

inductive_cases dstep_EnvXE[elim]: \<open>dstep RR FF CC (Env#\<rho>x, X) ss zz'\<close>
inductive_cases dstep_XEnvE[elim]: \<open>dstep RR FF CC (X, Env#\<rho>y) ss zz'\<close>

inductive_cases dstep_LocXE[elim]: \<open>dstep RR FF CC (Loc \<alpha>x#\<rho>x, X) ss zz'\<close>
inductive_cases dstep_XLocE[elim]: \<open>dstep RR FF CC (X, Loc \<alpha>y#\<rho>y) ss zz'\<close>


abbreviation pretty_dstep :: \<open>_ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> bool\<close>
  (\<open>_ =_, _, _, _\<Rightarrow> _\<close> [55,0,0,0,0,55] 55) where
  \<open>cc =RR, FF, CC, \<gamma>\<gamma>\<Rightarrow> cc' \<equiv> dstep RR FF CC \<gamma>\<gamma> cc cc'\<close>

inductive dsteps :: \<open>_ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> bool\<close> where
  dsteps_nil[intro!]: \<comment> \<open> safe as dstep is never ([],[])\<close>
  \<open>zz' = (((fst (fst ss)), snd (fst ss)), ((fst (snd ss)), snd (snd ss))) \<Longrightarrow>
    dsteps RR FF CC ([], []) ss zz'\<close>
| dsteps_step[intro]:
  \<open>dstep RR FF CC (\<rho>x, \<rho>y) ss ((sx', cy'), (sy', cy')) \<Longrightarrow>
    dsteps RR FF CC (\<rho>x', \<rho>y') ((sx', cy'), (sy', cy')) zz'' \<Longrightarrow>
    dsteps RR FF CC (\<rho>x @ \<rho>x', \<rho>y @ \<rho>y') ss zz''\<close>

inductive_cases dsteps_nilE[elim!]: \<open>dsteps RR FF CC ([], []) sc sc'\<close>
inductive_cases dsteps_cons_leftE[elim]: \<open>dsteps RR FF CC (\<alpha>\<^sub>ex # \<rho>x, \<rho>y) sc sc'\<close>
inductive_cases dsteps_cons_rightE[elim]: \<open>dsteps RR FF CC (\<rho>x, \<alpha>\<^sub>ey # \<rho>y) sc sc'\<close>

abbreviation dsteps_pretty :: \<open>_ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> bool\<close>
  (\<open>_ =_, _, _, _\<Rightarrow>\<^sup>* _\<close> [50, 0, 0, 0, 0, 50])
  where
    \<open>ss =RR, FF, CC, \<rho>xy\<Rightarrow>\<^sup>* zz' \<equiv> dsteps RR FF CC \<rho>xy ss zz'\<close>

lemma double_step_niltr_iff[simp]:
  \<open>(scx, scy) =RR, FF, CC, ([], [])\<Rightarrow>\<^sup>* (mscx', mscy') \<longleftrightarrow>
    fst mscx' = (fst scx) \<and> snd mscx' = snd scx \<and>
    fst mscy' = (fst scy) \<and> snd mscy' = snd scy\<close>
  apply (rule iffI)
   apply force
  apply (clarsimp, metis surjective_pairing)
  done
*)

section \<open> (Strong) Non-interference \<close>

definition
  \<open>rely_obs_safe \<oo> RR \<equiv>
    \<forall>hlx hly hsx hsy hsx' hsy'.
      \<bbbA> \<oo> ((hlx,hsx), (hly,hsy)) \<longrightarrow>
      RR (hsx, hsy) (hsx', hsy') \<longrightarrow>
      \<bbbA> \<oo> ((hlx, hsx'), (hly, hsy'))\<close>

definition                                                                      
  \<open>head_obs_determ \<oo> c \<equiv>
    (\<forall>ar. ar \<in># head_atoms c \<longrightarrow>
      (\<forall>br. br \<in># head_atoms c \<longrightarrow>
        (\<forall>x. Ex (ar x) \<longrightarrow>
          (\<forall>y. Ex (br y) \<longrightarrow>
            \<bbbA> \<oo> (x, y) \<longrightarrow>
            ar = br))))\<close>

definition                                                                      
  \<open>head_step_obs_safe \<oo> c \<equiv> \<lambda>(x, y).
      \<bbbA> \<oo> (x, y) \<longrightarrow>
        (\<forall>q x'. q \<in># head_atoms c \<longrightarrow> q x x' \<longrightarrow> \<bbbA> \<oo> (x', y)) \<and>
        (\<forall>q y'. q \<in># head_atoms c \<longrightarrow> q y y' \<longrightarrow> \<bbbA> \<oo> (x, y')) \<and>
        (\<forall>qx. qx \<in># head_atoms c \<longrightarrow>
          (\<forall>qy. qy \<in># head_atoms c \<longrightarrow>
          (\<forall>x'. qx x x' \<longrightarrow>
          (\<forall>y'. qy y y' \<longrightarrow>
            \<bbbA> \<oo> (x',y')))))\<close>


subsection \<open> Determinism \<close>
(*
subsubsection \<open> head domain \<close>

definition                                                                      
  \<open>heads_dom c \<equiv> \<Squnion>{p \<sqinter> pre_state q|p q. (p,q) \<in> head_atoms c}\<close>

lemma heads_domD:
  \<open>(p, q) \<in> head_atoms c \<Longrightarrow> p \<sqinter> pre_state q \<le> heads_dom c\<close>
  unfolding heads_dom_def
  by blast


subsubsection \<open> head could crash domain \<close>

definition                                                                      
  \<open>heads_ccrash_dom c \<equiv> \<Squnion>{-p|p q. (p,q) \<in> head_atoms c}\<close>

lemma heads_ccrash_domD:
  \<open>(p, q) \<in> head_atoms c \<Longrightarrow> -p \<le> heads_ccrash_dom c\<close>
  unfolding heads_ccrash_dom_def
  by blast
*)

subsubsection \<open> security deterministic endent \<close>

(*
definition
  \<open>sec_head_determ c \<equiv> \<lambda>(sx,sy).
    (\<forall>ca cb. ca \<^bold>\<box> cb \<in> all_subcomm_eq c \<longrightarrow>
      head_atomic ca \<and> head_atomic cb \<and>
      (\<forall>qa. qa \<in># head_atoms ca \<longrightarrow>
        (\<forall>qb. qb \<in># head_atoms cb \<longrightarrow>
          (pa sx \<noteq> pb sy) \<and>
          (pa sy \<noteq> pb sx)))) \<and>
    (\<forall>ca. DO ca OD \<in> all_subcomm_eq c \<longrightarrow>
      head_atomic ca \<and>
      (\<forall>pa qa. (pa,qa) \<in># head_atoms ca \<longrightarrow>
        pa sx = pa sy))\<close>

lemma sec_head_determ_comm_simps[simp]:
  \<open>sec_head_determ Skip ss = True\<close>
  \<open>sec_head_determ (c1 ;; c2) ss = (sec_head_determ c1 ss \<and> sec_head_determ c2 ss)\<close>
  \<open>sec_head_determ (c1 \<parallel> c2) ss = (sec_head_determ c1 ss \<and> sec_head_determ c2 ss)\<close>
  \<open>sec_head_determ (c1 \<^bold>\<sqinter> c2) ss = (sec_head_determ c1 ss \<and> sec_head_determ c2 ss)\<close>
  \<open>sec_head_determ (ca \<^bold>\<box> cb) (sx, sy) =
    (head_atomic ca \<and> head_atomic cb \<and>
      (\<forall>pa qa. (pa,qa) \<in># head_atoms ca \<longrightarrow>
        (\<forall>pb qb. (pb,qb) \<in># head_atoms cb \<longrightarrow>
          (pa sx \<noteq> pb sy) \<and>
          (pa sy \<noteq> pb sx))) \<and>
      sec_head_determ ca (sx, sy) \<and>
      sec_head_determ cb (sx, sy))\<close>
  \<open>sec_head_determ \<langle>ar\<rangle> ss = True\<close>
  \<open>sec_head_determ (DO ca OD) (sx, sy) =
    (head_atomic ca \<and>
      (\<forall>pa qa. (pa,qa) \<in># head_atoms ca \<longrightarrow>
        pa sx = pa sy) \<and>
      sec_head_determ ca (sx, sy))\<close>
  unfolding sec_head_determ_def
  by (clarsimp simp add: all_conj_distrib split: prod.splits; fast)+
*)

section \<open> Noninterference \<close>

definition doubled_atom
  :: \<open>(('l \<times> 'l) \<times> ('s \<times> 's) \<Rightarrow> ('l \<times> 'l) \<times> ('s \<times> 's) \<Rightarrow> bool) \<Rightarrow> bool\<close>
  where
    \<open>doubled_atom qq \<equiv> (\<exists>q. qq = liftR q \<circ>\<^sub>2 exch4)\<close>

lemma all_doubled_atom_liftC_iff[simp]:
  \<open>all_atom_comm doubled_atom (liftC c)\<close>
  by (induct c)
    (force simp add: doubled_atom_def)+


(*
section \<open> Double step aggregation lemmas \<close>

lemma two_aopstep_crash_then_same_post_comm:
  \<open>((sxl, sxs), c) \<midarrow>\<alpha>a\<rightarrow>\<^sub>a (Inr (), cx') \<Longrightarrow>
    ((syl, sys), c) \<midarrow>\<alpha>a\<rightarrow>\<^sub>a (Inr (), cy') \<Longrightarrow>
    sec_head_determ c ((sxl, sxs), (syl, sys)) \<Longrightarrow>
    cx' = cy'\<close>
  apply (induct c arbitrary: sxl syl sxs sys cx' cy' \<alpha>a)
        apply force
       apply force
      apply force
     apply force
    apply (clarsimp simp del: disj_not1 split: if_splits)
     apply (metis Inr_not_aopstep_tau_preserves_state split_pairs2)
    apply (elim disjE[of \<open>aopstep _ _ _\<close>]) (* 1 \<rightarrow> 4 *)
    (* 1/1 *)
       apply (simp add: vis_tau_aact_incompatible; fail)
    (* 1/2 *)
      apply (frule_tac sc=\<open>((sxl,_),_)\<close> in vis_aopstep_impl_atom, assumption)
      apply (frule_tac sc=\<open>((syl,_),_)\<close> in vis_aopstep_impl_atom, assumption)
      apply (simp add: vis_tau_aact_incompatible)
      apply blast
    (* 2/1 *)
     apply (frule_tac sc=\<open>((sxl,_),_)\<close> in vis_aopstep_impl_atom, assumption)
     apply (frule_tac sc=\<open>((syl,_),_)\<close> in vis_aopstep_impl_atom, assumption)
     apply (simp add: vis_tau_aact_incompatible)
     apply blast
    (* 2/2 *)
    apply (simp add: vis_tau_aact_incompatible; fail)
   apply (clarsimp split: if_splits; fail)
  apply force
  done

lemma double_step_crashI:
  \<open>((sxl, sxs), c) \<midarrow>\<alpha>a\<rightarrow>\<^sub>a (Inr (), c') \<Longrightarrow>
    ((syl, sys), c) \<midarrow>\<alpha>a\<rightarrow>\<^sub>a (Inr (), c') \<Longrightarrow>
    sec_head_determ c ((sxl, sxs), (syl, sys)) \<Longrightarrow>
    (((sxl, syl), (sxs, sys)), liftC c) \<midarrow>\<alpha>a\<rightarrow>\<^sub>a (Inr (), liftC c')\<close>
  apply (induct c arbitrary: sxl syl sxs sys c' \<alpha>a)
        apply force
       apply force
    (* parallel *)
      apply fastforce
    (* indet *)
     apply force
    (* endet *)
    apply (clarsimp split: if_splits)
     apply (metis Inl_Inr_False fst_conv aopstep_tau_preserves_state)
    apply (elim disjE) (* 1 \<rightarrow> 4 *)
    (** 1/1 *)
       apply (simp add: vis_tau_aact_incompatible; fail)
    (** 1/2 *)
      apply (frule_tac sc=\<open>((sxl,_),_)\<close> in vis_aopstep_impl_atom, assumption)
      apply (frule_tac sc=\<open>((syl,_),_)\<close> in vis_aopstep_impl_atom, assumption)
      apply (simp add: vis_tau_aact_incompatible)
      apply blast
    (** 2/1 *)
     apply (frule_tac sc=\<open>((sxl,_),_)\<close> in vis_aopstep_impl_atom, assumption)
     apply (frule_tac sc=\<open>((syl,_),_)\<close> in vis_aopstep_impl_atom, assumption)
     apply (simp add: vis_tau_aact_incompatible)
     apply blast
    (** 2/2 *)
    apply (simp add: vis_tau_aact_incompatible; fail)
    (* atom *)
   apply (clarsimp split: if_splits; fail)
    (* do-loop *)
  apply clarsimp
  apply (metis two_aopstep_crash_then_same_post_comm)
  done

lemma double_no_stepI:
  \<open>((sxl, sxs), c) \<midarrow>\<sslash>\<rightarrow>\<^sub>a \<Longrightarrow>
    ((syl, sys), c) \<midarrow>\<sslash>\<rightarrow>\<^sub>a \<Longrightarrow>
    (((sxl, syl), (sxs, sys)), liftC c) \<midarrow>\<sslash>\<rightarrow>\<^sub>a\<close>
  apply (induct c arbitrary: sxl syl sxs sys)
    (* Skip *)
        apply force
    (* Seq *)
       apply (clarsimp, metis)
    (* Parallel *)
      apply simp
      apply (intro allI conjI impI)
        apply metis
       apply metis
      apply metis
    (* INDet *)
     apply (simp, fast)
    (* ENDet *)
    apply (clarsimp, metis)
    (* Atom *)
   apply (simp, fastforce)
    (* DoLoop *)
  apply (simp, metis)
  done

lemma no_step_then_no_two_step:
  \<open>((sxl, sxs), c) \<midarrow>/\<rightarrow>\<^sub>a \<Longrightarrow>
    ((syl, sys), c) \<midarrow>/\<rightarrow>\<^sub>a \<Longrightarrow>
    (((sxl, syl), (sxs, sys)), liftC c) \<midarrow>/\<rightarrow>\<^sub>a\<close>
  apply (induct c arbitrary: sxl syl sxs sys)
    (* Skip *)
        apply force
    (* Seq *)
       apply (clarsimp, metis)
    (* Parallel *)
      apply simp
      apply (intro allI conjI impI)
        apply metis
       apply metis
      apply metis
    (* INDet *)
     apply (simp, fast)
    (* ENDet *)
    apply (clarsimp, metis)
    (* Atom *)
   apply (simp, fastforce)
    (* DoLoop *)
  apply (simp, metis)
  done

lemma double_no_tau_aopstep:
  assumes
    \<open>\<forall>s' c'. \<not> ((sxl, sxs), c) \<midarrow>\<alpha>a\<rightarrow>\<^sub>a (s', c')\<close>
    \<open>\<forall>s' c'. \<not> ((syl, sys), c) \<midarrow>\<alpha>a\<rightarrow>\<^sub>a (s', c')\<close>
    \<open>tau_aact \<alpha>a\<close>
  shows
    \<open>\<forall>s' c'. \<not> (((sxl, syl), (sxs, sys)), liftC c) \<midarrow>\<alpha>a\<rightarrow>\<^sub>a (s', c')\<close>
  using assms
proof (induct c arbitrary: \<alpha>a sxl syl sxs sys)
  case Skip
  then show ?case by force
next
  case (Seq c1 c2)
  then show ?case
    by (clarsimp, metis)
next
  case (Par c1 c2)
  show ?case
    using Par.prems
    apply clarsimp
    apply (intro conjI)
      apply blast
     apply (clarsimp simp add: Par.hyps(1); fail)
    apply (clarsimp simp add: Par.hyps(2); fail)
    done
next
  case (Indet c1 c2)
  then show ?case
    by (simp, metis)
next
  case (Endet c1 c2)
  then show ?case
    by (simp, fast)
next
  case (Atomic p q)
  then show ?case
    by clarsimp
next
  case (Iter c)
  then show ?case
    apply (clarsimp simp add: all_conj_distrib)
    oops


lemma double_step_endent_tau_helper1:
  \<open>(\<alpha>a = TauBasic \<and> c1 = Skip \<and> syl' = syl \<and> sys' = sys \<and> c' = c2 \<or>
      \<alpha>a = TauBasic \<and> c2 = Skip \<and> syl' = syl \<and> sys' = sys \<and> c' = c1 \<or>
      (\<exists>c1'. c' = c1' \<^bold>\<box> c2 \<and> ((syl, sys), c1) \<midarrow>\<alpha>a\<rightarrow>\<^sub>a ((syl', sys'), c1')) \<or>
      (\<exists>c2'. c' = c1 \<^bold>\<box> c2' \<and> ((syl, sys), c2) \<midarrow>\<alpha>a\<rightarrow>\<^sub>a ((syl', sys'), c2'))) \<and>
    (\<alpha>a = TauBasic \<and> c1 = Skip \<and> sxl' = sxl \<and> sxs' = sxs \<and> c' = c2 \<or>
      \<alpha>a = TauBasic \<and> c2 = Skip \<and> sxl' = sxl \<and> sxs' = sxs \<and> c' = c1 \<or>
      (\<exists>c1'. c' = c1' \<^bold>\<box> c2 \<and> ((sxl, sxs), c1) \<midarrow>\<alpha>a\<rightarrow>\<^sub>a ((sxl', sxs'), c1')) \<or>
      (\<exists>c2'. c' = c1 \<^bold>\<box> c2' \<and> ((sxl, sxs), c2) \<midarrow>\<alpha>a\<rightarrow>\<^sub>a ((sxl', sxs'), c2'))) \<longleftrightarrow>
    (\<exists>c1'. c' = c1' \<^bold>\<box> c2 \<and>
      ((syl, sys), c1) \<midarrow>\<alpha>a\<rightarrow>\<^sub>a ((syl', sys'), c1') \<and>
      ((sxl, sxs), c1) \<midarrow>\<alpha>a\<rightarrow>\<^sub>a ((sxl', sxs'), c1')) \<or>
    (\<exists>c2'. c' = c1 \<^bold>\<box> c2' \<and>
      ((syl, sys), c2) \<midarrow>\<alpha>a\<rightarrow>\<^sub>a ((syl', sys'), c2') \<and>
      ((sxl, sxs), c2) \<midarrow>\<alpha>a\<rightarrow>\<^sub>a ((sxl', sxs'), c2')) \<or>
    (\<alpha>a = TauBasic \<and> c1 = Skip \<and> c2 = c' \<or>
      \<alpha>a = TauBasic \<and> c1 = c' \<and> c2 = Skip) \<and>
      sxl' = sxl \<and> sxs' = sxs \<and> syl' = syl \<and> sys' = sys\<close>
  apply (simp add: conj_disj_distribL conj_disj_distribR)
  apply (rule iffI)
   apply (elim disjE)
                  apply force
                 apply force
                apply force
               apply (metis Pair_inject aopstep_endet_skip_then(2))
              apply force
             apply force
            apply (metis Pair_inject aopstep_endet_skip_then(1))
           apply force
          apply (metis aopstep.simps(1))
         apply (metis Pair_inject aopstep_endet_skip_then(1))
        apply force
       apply force
      apply force
     apply (metis aopstep.simps(1))
    apply force
   apply force
  apply (elim disjE; metis)
  done

lemma same_start_two_aopstep_then_same_result_comm:
  \<open>(sx, c) \<midarrow>\<alpha>\<rightarrow>\<^sub>a (sx', cx') \<Longrightarrow>
    (sy, c) \<midarrow>\<alpha>\<rightarrow>\<^sub>a (sy', cy') \<Longrightarrow>
    sec_head_determ c (sx, sy) \<Longrightarrow>
    cx' = cy'\<close>
  apply (induct c arbitrary: \<alpha> sx sx' cx' sy sy' cy')
        apply fastforce
       apply fastforce
      apply fastforce
     apply fastforce
    (* endet *)
    apply (clarsimp simp add: if_bool_eq_disj)
    apply (subgoal_tac \<open>c1 = Skip \<and> c2 = Skip \<or> c1 \<noteq> Skip \<and> c2 \<noteq> Skip\<close>)
     prefer 2
     apply (metis head_atomic.simps(1))
    apply (erule disjE[of \<open>_ \<and> _\<close> \<open>_ \<and> _\<close>])
     apply force
    apply clarsimp
    apply (case_tac \<open>vis_aact \<alpha>\<close>)
     apply (clarsimp simp add: vis_tau_aact_incompatible)
     apply (elim disjE)
        apply blast
       apply (frule_tac sc=\<open>(_,c1)\<close> in vis_aopstep_impl_atom, fast)
       apply (frule_tac sc=\<open>(_,c2)\<close> in vis_aopstep_impl_atom, fast)
       apply clarsimp
       apply blast
      apply (frule_tac sc=\<open>(_,c1)\<close> in vis_aopstep_impl_atom, fast)
      apply (frule_tac sc=\<open>(_,c2)\<close> in vis_aopstep_impl_atom, fast)
      apply clarsimp
      apply blast
     apply blast
    apply clarsimp
    apply (elim disjE) (* +3 *)
       apply blast
      apply clarsimp
      apply (frule_tac sc=\<open>(_,c1)\<close> in aopstep_tau_preserves_state, fast)
      apply (frule_tac sc=\<open>(_,c2)\<close> in aopstep_tau_preserves_state, fast)
      apply clarsimp
  subgoal sorry
  subgoal sorry
    apply blast
    (* atom *)
   apply (clarsimp split: if_splits; fail)
    (* do-loop *)
  apply clarsimp
  apply (elim disjE)
     apply blast
    apply clarsimp
  subgoal sorry
  oops


lemma aopstep_then_pair_aopstep:
  \<open>(sx, c) \<midarrow>\<alpha>a\<rightarrow>\<^sub>a (sx', c') \<Longrightarrow>
    (sy, c) \<midarrow>\<alpha>a\<rightarrow>\<^sub>a (sy', c') \<Longrightarrow>
    sec_head_determ c (sx, sy) \<Longrightarrow>
    (((fst sx, fst sy), (snd sx, snd sy)), liftC c)
      \<midarrow>\<alpha>a\<rightarrow>\<^sub>a (((fst sx', fst sy'), (snd sx', snd sy')), liftC c')\<close>
  apply (induct c arbitrary: sx sy sx sy c' \<alpha>a)
    (* Skip *)
        apply force
    (* Seq *)
       apply clarsimp
       apply (elim disjE)
          apply force
         apply force
        apply force
       apply (clarsimp, metis)
    (* Parallel *)
      apply clarsimp
      apply (elim disjE; clarsimp; metis)
      (* INDet *)
     apply fastforce
      (* ENDet *)
    apply (cases sx', cases sy')
    apply (clarsimp del: disjCI simp del: disj_not1)
    apply (rename_tac sxl' sxs' syl' sys')
    apply (clarsimp del: disjCI simp del: disj_not1 split: if_splits)
    (** Tau *)
     apply (simp add: vis_tau_aact_incompatible del: disj_not1)
     apply (drule(1) iffD1[OF double_step_endent_tau_helper1, OF conjI])+
     apply (thin_tac \<open>_ \<or> _ \<or> _ \<or> _\<close>)+
     apply (elim disjE)
       apply metis
      apply metis
     apply metis
    (** non-Tau *)
    apply (subgoal_tac \<open>\<alpha>a \<noteq> TauBasic\<close>)
     prefer 2
     apply force
    apply simp
    apply (elim disjE)
    (*** 1/1 *)
       apply (metis not_vis_aact_iff)
    (*** 2/1: forbidden *)
      apply (frule_tac sc=\<open>(_,c1)\<close> in vis_aopstep_impl_atom, assumption)
      apply (frule_tac sc=\<open>(_,c2)\<close> in vis_aopstep_impl_atom, assumption)
      apply clarsimp
      apply blast
    (*** 1/2: forbidden *)
     apply (frule_tac sc=\<open>(_,c1)\<close> in vis_aopstep_impl_atom, assumption)
     apply (frule_tac sc=\<open>(_,c2)\<close> in vis_aopstep_impl_atom, assumption)
     apply clarsimp
     apply blast
    (*** 2/2 *)
    apply (metis not_vis_aact_iff)
    (* Atom *)
   apply (clarsimp split: if_splits; fail)
    (* Do-loop *)
  apply (clarsimp del: disjCI)
  apply (subgoal_tac \<open>c' = Skip \<or> (\<exists>ca cb. c' = ca ;; DO cb OD)\<close>)
   prefer 2
   apply blast
  apply (rename_tac sxl' sxs' syl' sys' c' \<alpha>)
  apply (erule disjE[of \<open>_ = _\<close> \<open>Ex _\<close>])
    (* in order to complete a do-loop, it must be impossible for the sub-program
        to take a step. *)
   apply (case_tac \<open>\<alpha> \<noteq> TauBasic\<close>, force)
   apply clarsimp
   apply (metis no_aopstep_rgstate_iff no_step_then_no_two_step)
  apply force
  done


lemma strong_aopstep_then_pair_aopstep:
  \<open>(sx, c) \<midarrow>\<alpha>a\<rightarrow>\<^sub>a (sx', c') \<Longrightarrow>
    (sy, c) \<midarrow>\<alpha>a\<rightarrow>\<^sub>a (sy', c') \<Longrightarrow>
    sec_head_determ c (sx, sy) \<Longrightarrow>
    (((fst sx, fst sy), (snd sx, snd sy)), liftC c)
      \<midarrow>\<alpha>a\<rightarrow>\<^sub>a (((fst sx', fst sy'), (snd sx', snd sy')), liftC c')\<close>
  apply (induct c arbitrary: sx sy sx sy c' \<alpha>a)
    (* Skip *)
        apply force
    (* Seq *)
       apply clarsimp
       apply (elim disjE)
          apply force
         apply force
        apply force
       apply (clarsimp, metis)
    (* Parallel *)
      apply clarsimp
      apply (elim disjE; clarsimp; metis)
      (* INDet *)
     apply fastforce
      (* ENDet *)
    apply (cases sx', cases sy')
    apply (clarsimp del: disjCI simp del: disj_not1)
    apply (rename_tac sxl' sxs' syl' sys')
    apply (clarsimp del: disjCI simp del: disj_not1 split: if_splits)
    (** Tau *)
     apply (simp add: vis_tau_aact_incompatible del: disj_not1)
     apply (drule(1) iffD1[OF double_step_endent_tau_helper1, OF conjI])+
     apply (thin_tac \<open>_ \<or> _ \<or> _ \<or> _\<close>)+
     apply (elim disjE)
       apply metis
      apply metis
     apply metis
    (** non-Tau *)
    apply (subgoal_tac \<open>\<alpha>a \<noteq> TauBasic\<close>)
     prefer 2
     apply force
    apply simp
    apply (elim disjE)
    (*** 1/1 *)
       apply (metis not_vis_aact_iff)
    (*** 2/1: forbidden *)
      apply (frule_tac sc=\<open>(_,c1)\<close> in vis_aopstep_impl_atom, assumption)
      apply (frule_tac sc=\<open>(_,c2)\<close> in vis_aopstep_impl_atom, assumption)
      apply clarsimp
      apply blast
    (*** 1/2: forbidden *)
     apply (frule_tac sc=\<open>(_,c1)\<close> in vis_aopstep_impl_atom, assumption)
     apply (frule_tac sc=\<open>(_,c2)\<close> in vis_aopstep_impl_atom, assumption)
     apply clarsimp
     apply blast
    (*** 2/2 *)
    apply (metis not_vis_aact_iff)
    (* Atom *)
   apply (clarsimp split: if_splits; fail)
    (* Do-loop *)
  apply (clarsimp del: disjCI)
  apply (subgoal_tac \<open>c' = Skip \<or> (\<exists>ca cb. c' = ca ;; DO cb OD)\<close>)
   prefer 2
   apply blast
  apply (rename_tac sxl' sxs' syl' sys' c' \<alpha>)
  apply (erule disjE[of \<open>_ = _\<close> \<open>Ex _\<close>])
    (* in order to complete a do-loop, it must be impossible for the sub-program
        to take a step. *)
   apply (case_tac \<open>\<alpha> \<noteq> TauBasic\<close>, force)
   apply clarsimp
   apply (metis no_aopstep_rgstate_iff no_step_then_no_two_step)
  apply force
  done
*)

section \<open> Non-interference \<close>

lemma aopsteps_Skip_iif[simp]:
  \<open>(s, Skip) \<midarrow>\<rho>\<rightarrow>\<^sub>a\<^sup>* sc'' \<longleftrightarrow> sc'' = (s, Skip) \<and> \<rho> = []\<close>
  by (cases sc'', induct \<rho>; force)


section \<open> Basic Tau Reducts \<close>

text \<open>
  Uunfortunately dependent on the state the command is executed in, because of loops.
\<close>
definition basic_tau_reducts :: \<open>'l \<times> 's \<Rightarrow> ('l \<times> 's) comm \<Rightarrow> ('l \<times> 's) comm set\<close> where
  \<open>basic_tau_reducts s c \<equiv>
    {c'. \<exists>\<rho> s'.
      (s, c) \<midarrow>\<rho>\<rightarrow>\<^sub>a\<^sup>* (s', c') \<and>
      list_all basic_tau_aact \<rho> \<and>
      ((\<exists>\<alpha> s'' c''. (s', c') \<midarrow>\<alpha>\<rightarrow>\<^sub>a (s'', c'') \<and> \<not> basic_tau_aact \<alpha>) \<or>
        (s', c') \<midarrow>/\<rightarrow>\<^sub>a)}\<close>


lemma btr_seq_left[intro]:
  assumes
    \<open>ca' \<in> basic_tau_reducts s ca\<close>
    \<open>ca' \<noteq> Skip\<close>
  shows
    \<open>ca' ;; cb \<in> basic_tau_reducts s (ca ;; cb)\<close>
  using assms
proof (clarsimp simp add: basic_tau_reducts_def simp del: split_paired_Ex)
  fix sl' ss' c' \<rho> sl'' ss'' \<alpha>
  assume assms2:
    \<open>(s, ca) \<midarrow>\<rho>\<rightarrow>\<^sub>a\<^sup>* ((sl', ss'), c')\<close>
    \<open>list_all basic_tau_aact \<rho>\<close>
    \<open>\<not> basic_tau_aact \<alpha>\<close>
    \<open>((sl', ss'), c') \<midarrow>\<alpha>\<rightarrow>\<^sub>a ((sl'', ss''), ca')\<close>
  moreover then have
    \<open>(s, ca ;; cb) \<midarrow>\<rho>\<rightarrow>\<^sub>a\<^sup>* ((sl', ss'), c' ;; cb)\<close>
    apply (induct \<rho> arbitrary: ca ca')
     apply force
    apply (rename_tac \<alpha> \<rho> ca ca')
    apply clarsimp
    apply (rename_tac slx ssx cx)
    apply (metis (no_types, opaque_lifting) aopstep_tau_preserves_state
        basic_tau_aact_then_tau_aact fst_conv sum.sel(1))
    done
  oops
(*
  ultimately show
    \<open>\<exists>\<rho> s' c'.
      (s, ca ;; cb) \<midarrow>\<rho>\<rightarrow>\<^sub>a\<^sup>* (s', c') \<and>
      list_all basic_tau_aact \<rho> \<and>
      (\<exists>\<alpha>. (\<exists>s''. (s', c') \<midarrow>\<alpha>\<rightarrow>\<^sub>a (s'', ca' ;; cb)) \<and>
            \<not> basic_tau_aact \<alpha>)\<close>
    using assms2
    by (meson aopstep_then_aopstep_right_seqD)
qed
*)
(*
| btr_seq_right[intro]:
  \<open>basic_tau_reducts s ca Skip \<Longrightarrow>
    basic_tau_reducts s cb cb' \<Longrightarrow>
    basic_tau_reducts s (ca ;; cb) cb'\<close>
| btr_indet[intro!]:
  \<open>basic_tau_reducts s (ca \<^bold>\<sqinter> cb) (ca \<^bold>\<sqinter> cb)\<close>
| btr_endet_nonskip[intro]:
  \<open>basic_tau_reducts s ca ca' \<Longrightarrow> ca' \<noteq> Skip \<Longrightarrow>
    basic_tau_reducts s cb cb' \<Longrightarrow> cb' \<noteq> Skip \<Longrightarrow>
    basic_tau_reducts s (ca \<^bold>\<box> cb) (ca' \<^bold>\<box> cb')\<close>
| btr_endet_skip_left[intro]:
  \<open>basic_tau_reducts s ca Skip \<Longrightarrow>
    basic_tau_reducts s cb cb' \<Longrightarrow>
    basic_tau_reducts s (ca \<^bold>\<box> cb) cb'\<close>
| btr_endet_skip_right[intro]:
  \<open>basic_tau_reducts s ca ca' \<Longrightarrow>
    basic_tau_reducts s cb Skip \<Longrightarrow>
    basic_tau_reducts s (ca \<^bold>\<box> cb) ca'\<close>
| btr_par_nonend[intro]:
  \<open>basic_tau_reducts s ca ca' \<Longrightarrow>
    basic_tau_reducts s cb cb' \<Longrightarrow>
    ca' \<noteq> Skip \<or> cb' \<noteq> Skip \<Longrightarrow>
    basic_tau_reducts s (ca \<parallel> cb) (ca' \<parallel> cb')\<close>
| btr_par_end[intro]:
  \<open>basic_tau_reducts s ca Skip \<Longrightarrow>
    basic_tau_reducts s cb Skip \<Longrightarrow>
    basic_tau_reducts s (ca \<parallel> cb) Skip\<close>
| btr_loop_done[intro]:
  \<open>(s, c) \<midarrow>/\<rightarrow>\<^sub>a \<Longrightarrow> basic_tau_reducts s (DO ca OD) Skip\<close>
| btr_loop_steps[intro]:
  \<open>\<not> ((s, c) \<midarrow>/\<rightarrow>\<^sub>a) \<Longrightarrow>
    basic_tau_reducts s ca ca' \<Longrightarrow>
    basic_tau_reducts s (ca' ;; DO ca OD) cx \<Longrightarrow>
    basic_tau_reducts s (DO ca OD) cx\<close>
| btr_atom[intro!]:
  \<open>basic_tau_reducts s (Atomic pa qa) (Atomic pa qa)\<close>

inductive_cases btr_skipE[elim!]: \<open>basic_tau_reducts s Skip c'\<close>
inductive_cases btr_seqE[elim]: \<open>basic_tau_reducts s (ca ;; cb) c'\<close>
inductive_cases btr_indetE[elim!]: \<open>basic_tau_reducts s (ca \<^bold>\<sqinter> cb) c'\<close>
inductive_cases btr_endetE[elim]: \<open>basic_tau_reducts s (ca \<^bold>\<box> cb) c'\<close>
inductive_cases btr_parE[elim]: \<open>basic_tau_reducts s (ca \<parallel> cb) c'\<close>
inductive_cases btr_loopE[elim]: \<open>basic_tau_reducts s (DO ca OD) c'\<close>
inductive_cases btr_atomE[elim!]: \<open>basic_tau_reducts s \<langle>pa, qa\<rangle> c'\<close>
*)

lemma btr_skip_left_iff[simp]:
  \<open>c' \<in> basic_tau_reducts s Skip \<longleftrightarrow> c' = Skip\<close>
  unfolding basic_tau_reducts_def
  sorry
(*
  by (metis aopsteps_iff(1) list_all_simps(2) prod.inject surj_pair)
*)

lemma basic_tau_reducts_from_basic_tau_step:
  \<open>(s, c) \<midarrow>\<alpha>\<rightarrow>\<^sub>a (ms', c') \<Longrightarrow>
    c' \<in> basic_tau_reducts s c \<Longrightarrow>
    ms' = s \<and> basic_tau_aact \<alpha>\<close>
  apply (induct c arbitrary: \<alpha> s ms' c')
        apply force
       apply clarsimp
  oops

lemma no_aopstep_then_basic_tau_reduct_false[simp]:
  \<open>(s, c) \<midarrow>/\<rightarrow>\<^sub>a \<Longrightarrow> c' \<in> basic_tau_reducts s c \<longleftrightarrow> c' = c\<close>
  unfolding basic_tau_reducts_def
  apply clarsimp
  apply (rule iffI)
   apply clarsimp
   apply (erule aopsteps.cases; force)
  apply clarsimp
  apply (metis aopsteps_nil fst_conv list_all_simps(2) snd_conv surjective_pairing)
  done


lemma basic_tau_reducts_step_trans:
  \<open>(s, c) \<midarrow>\<alpha>\<rightarrow>\<^sub>a (s', c') \<Longrightarrow>
    basic_tau_aact \<alpha> \<Longrightarrow>
    c'' \<in> basic_tau_reducts s' c' \<Longrightarrow>
    c'' \<in> basic_tau_reducts s c\<close>
  apply (clarsimp simp add: basic_tau_reducts_def)
  oops

lemma basic_tau_aact_exclusive:
  \<open>sc \<midarrow>\<alpha>\<rightarrow>\<^sub>a sc' \<Longrightarrow>
    basic_tau_aact \<alpha> \<Longrightarrow>
    sc \<midarrow>\<alpha>'\<rightarrow>\<^sub>a sc' \<Longrightarrow>
    basic_tau_aact \<alpha>'\<close>
  apply (frule aopstep_tau_preserves_state, force)
  apply (induct \<alpha> sc sc' arbitrary: \<alpha>' rule: aopstep.induct)
        apply force
       apply force
      apply force
    (* endet *)
     apply (clarsimp simp add: if_bool_eq_disj)
     apply (rename_tac s' c' \<alpha>')
     apply (case_tac \<open>ca = Skip \<and> cb = Skip\<close>)
      apply force
     apply (clarsimp simp add:
      vis_tau_aact_incompatible(2)[OF basic_tau_aact_then_tau_aact])
     apply (elim disjE conjE exE)
                      apply (simp; fail)+
                      apply (clarsimp, blast)
                      apply (simp; fail)+
                  apply (clarsimp, blast)
                 apply (simp; fail)+
          apply clarsimp
          apply (frule(1) vis_aopstep_backwards_endet, force)
          apply (clarsimp simp only: fst_conv snd_conv)
  subgoal sorry
         apply (simp; fail)+
     apply clarsimp
  subgoal sorry
      (* par *)
    apply clarsimp
    apply (elim disjE, (force+)[5])
       apply (clarify, metis basic_tau_aact.simps(5))
      apply (clarify, meson self_aopstep_impossible(1); fail)
     apply (clarify, meson self_aopstep_impossible(1); fail)
    apply (clarify, metis basic_tau_aact.simps(6))
    (* do-loop *)
   apply (clarsimp, blast)
    (* atom *)
  apply force
  oops

lemma basic_tau_reducts_from_basic_tau_exec:
  \<open>sc \<midarrow>\<rho>\<rightarrow>\<^sub>a\<^sup>* sc' \<Longrightarrow>
    sc = (s, c) \<Longrightarrow>
    sc' = (ms', c') \<Longrightarrow>
    sc \<midarrow>\<rho>y\<rightarrow>\<^sub>a\<^sup>* sc' \<Longrightarrow>
    list_all basic_tau_aact \<rho>y \<Longrightarrow>
    length \<rho> \<le> length \<rho>y \<Longrightarrow>
    ms' = s \<and> list_all basic_tau_aact \<rho>\<close>
  apply (induct arbitrary: s c ms' c' rule: aopsteps.induct)
    apply force
   apply clarsimp
  oops

(*
lemma basic_tau_equiv_dstep_secure:
  \<open>xyc =RR, FF, CC, (\<sigma>x, \<sigma>y)\<Rightarrow> xyc' \<Longrightarrow>
    xyc = ((tx, cx), (ty, cy)) \<Longrightarrow>
    xyc' = ((tx', cx'), (ty', cy')) \<Longrightarrow>
    list_all basic_tau_aact (etrace_aact_reduce \<sigma>x) \<Longrightarrow>
    list_all basic_tau_aact (etrace_aact_reduce \<sigma>y) \<Longrightarrow>
    basic_tau_succ (tx, cx) = basic_tau_succ (tx', cx') \<Longrightarrow>
    basic_tau_succ (ty, cy) = basic_tau_succ (tx', cy') \<Longrightarrow>
    rely_obs_safe \<oo> RR \<Longrightarrow>
    \<bbbA> \<oo> (tx, ty) \<Longrightarrow>
    \<bbbA> \<oo> (tx', ty')\<close>
proof (induct arbitrary: tx cx ty cy tx' cx' ty' cy' rule: dstep.induct)
  case (dstep_env RR sx sy sx' sy' CC cxx cyy FF lx ly)
  then show ?case
    unfolding rely_obs_safe_def
    by fast
next
  case (dstep_local FF fx fy sx sy CC cxx cyy lx \<rho>x lx' sx' cxx' ly \<rho>y ly' sy' cyy' RR)
  then show ?case
    apply clarsimp
    sorry
  oops


subsubsection \<open> extract left/right from opstep \<close>

lemma no_liftC_opstep_then_no_fst_opstep:
  \<open>((ll, ss), liftC c) \<midarrow>/\<rightarrow> \<Longrightarrow> ((fst ll, fst ss), c) \<midarrow>/\<rightarrow>\<close>
  apply (induct c)
        apply force
       apply clarsimp
  sorry

lemma double_opstep_implies_fst_opstep:
  \<open>sscc \<midarrow>\<alpha>\<rightarrow> msscc' \<Longrightarrow>
    sscc = ((ll, ss), liftC c) \<Longrightarrow>
    msscc' = ((ll', ss'), cc') \<Longrightarrow>
    ((fst ll, fst ss), c) \<midarrow>\<alpha>\<rightarrow> ((fst ll', fst ss'), unliftC cc')\<close>
  apply (induct \<alpha> sscc msscc' arbitrary: ll ss c ll' ss' cc' rule: opstep.induct)
        apply fastforce
       apply fastforce
      apply fastforce
     apply (clarsimp simp add: if_bool_eq_disj)
     apply (metis act.distinct(1) unliftC_simp(5) unliftC_liftC_cancel)
    apply fastforce
   apply (clarsimp simp add: unliftC_rev_iff)
  apply (rename_tac la lb sa sb la' lb' sa' sb' c' c)
   apply (rule conjI)
    apply (elim disjE)
     apply clarsimp
     apply (force dest: no_liftC_opstep_then_no_fst_opstep[simplified])
    apply fastforce
   apply fastforce
  apply (force simp add: if_bool_eq_disj)
  done

lemma no_liftC_opstep_then_no_snd_opstep:
  \<open>((ll, ss), liftC c) \<midarrow>/\<rightarrow> \<Longrightarrow> ((snd ll, snd ss), c) \<midarrow>/\<rightarrow>\<close>
  apply (induct c)
        apply force
       apply clarsimp
  sorry

lemma double_opstep_implies_snd_opstep:
  \<open>sscc \<midarrow>\<alpha>\<rightarrow> msscc' \<Longrightarrow>
    sscc = ((ll, ss), liftC c) \<Longrightarrow>
    msscc' = ((ll', ss'), cc') \<Longrightarrow>
    ((snd ll, snd ss), c) \<midarrow>\<alpha>\<rightarrow> ((snd ll', snd ss'), unliftC cc')\<close>
  apply (induct \<alpha> sscc msscc' arbitrary: ll ss c ll' ss' cc' rule: opstep.induct)
        apply fastforce
       apply fastforce
      apply fastforce
     apply (clarsimp simp add: if_bool_eq_disj)
     apply (metis tau_aact_def tau_aact_simps(4) unliftC_simp(5) unliftC_liftC_cancel
      vis_aact_simps(4) vis_aact_unit_def)
    apply fastforce
   apply (clarsimp simp add: unliftC_rev_iff)
   apply (rename_tac la lb sa sb la' lb' sa' sb' c' c)
   apply (rule conjI)
    apply (elim disjE)
     apply clarsimp
     apply (force dest: no_liftC_opstep_then_no_snd_opstep[simplified])
    apply fastforce
   apply fastforce
  apply (force simp add: if_bool_eq_disj)
  done

subsubsection \<open> extract left/right from aopstep \<close>

lemma no_liftC_aopstep_then_no_fst_aopstep:
  \<open>((ll, ss), liftC c) \<midarrow>/\<rightarrow>\<^sub>a \<Longrightarrow> ((fst ll, fst ss), c) \<midarrow>/\<rightarrow>\<^sub>a\<close>
  apply (induct c)
        apply force
       apply clarsimp
  sorry

lemma double_aopstep_implies_fst_opstep:
  \<open>sscc \<midarrow>\<alpha>\<rightarrow>\<^sub>a msscc' \<Longrightarrow>
    sscc = ((ll, ss), liftC c) \<Longrightarrow>
    msscc' = ((ll', ss'), cc') \<Longrightarrow>
    ((fst ll, fst ss), c) \<midarrow>\<alpha>\<rightarrow>\<^sub>a ((fst ll', fst ss'), unliftC cc')\<close>
  apply (induct \<alpha> sscc msscc' arbitrary: ll ss c ll' ss' cc' rule: aopstep_induct)
        apply fastforce
       apply fastforce
      apply fastforce
     apply (clarsimp simp add: if_bool_eq_disj)
     apply (metis strip_aact.simps(2) tau_aact_def tau_aact_simps(3)
      unliftC_simp(5) unliftC_liftC_cancel vis_aact_unit_def)
    apply fastforce
   apply (clarsimp simp add: unliftC_rev_iff)
  apply (rename_tac la lb sa sb la' lb' sa' sb' c' c)
   apply (rule conjI)
    apply (elim disjE)
     apply clarsimp
     apply (force dest: no_liftC_aopstep_then_no_fst_aopstep[simplified])
    apply fastforce
   apply fastforce
  apply (force simp add: if_bool_eq_disj)
  done

lemma no_liftC_aopstep_then_no_snd_aopstep:
  \<open>((ll, ss), liftC c) \<midarrow>/\<rightarrow>\<^sub>a \<Longrightarrow> ((snd ll, snd ss), c) \<midarrow>/\<rightarrow>\<^sub>a\<close>
  apply (induct c)
        apply force
       apply clarsimp
  sorry

lemma double_aopstep_implies_snd_opstep:
  \<open>sscc \<midarrow>\<alpha>\<rightarrow>\<^sub>a msscc' \<Longrightarrow>
    sscc = ((ll, ss), liftC c) \<Longrightarrow>
    msscc' = ((ll', ss'), cc') \<Longrightarrow>
    ((snd ll, snd ss), c) \<midarrow>\<alpha>\<rightarrow>\<^sub>a ((snd ll', snd ss'), unliftC cc')\<close>
  apply (induct \<alpha> sscc msscc' arbitrary: ll ss c ll' ss' cc' rule: aopstep_induct)
        apply fastforce
       apply fastforce
      apply fastforce
     apply (clarsimp simp add: if_bool_eq_disj)
     apply (metis strip_aact.simps(2) tau_aact_def tau_aact_simps(3)
      unliftC_simp(5) unliftC_liftC_cancel vis_aact_unit_def)
    apply fastforce
   apply (clarsimp simp add: unliftC_rev_iff)
   apply (rename_tac la lb sa sb la' lb' sa' sb' c' c)
   apply (rule conjI)
    apply (elim disjE)
     apply clarsimp
     apply (force dest: no_liftC_aopstep_then_no_snd_aopstep[simplified])
    apply fastforce
   apply fastforce
  apply (force simp add: if_bool_eq_disj)
  done


subsubsection \<open> from aopstep to double-step \<close>

lemma aopstep_implies_double_step:
  fixes sx :: \<open>'l::pre_perm_alg \<times> 's\<close>
  assumes
    \<open>sfsfcc \<midarrow>\<alpha>\<rightarrow>\<^sub>a sfsfcc'\<close>
    \<open>sfsfcc = (((fst sx + fx, fst sy + fy), snd sx, snd sy), liftC c)\<close>
    \<open>sfsfcc' = (((fst sx' + fx, fst sy' + fy), snd sx', snd sy'), cc')\<close>
    \<open>(=) \<le> CC\<close>
    \<open>FF ((fx, fy), snd sx, snd sy)\<close>
    \<open>fst sx ## fx\<close>
    \<open>fst sy ## fy\<close>
    \<open>FF ((fx, fy), snd sx', snd sy')\<close>
    \<open>fst sx' ## fx\<close>
    \<open>fst sy' ## fy\<close>
  shows
    \<open>(((sx, c), sy, c)
      =RR, FF, CC, ([Loc \<alpha>], [Loc \<alpha>])\<Rightarrow>
      ((sx', unliftC cc'), sy', unliftC cc'))\<close>
proof -
  have left_step:
    \<open>((fst sx + fx, snd sx), c) \<midarrow>\<alpha>\<rightarrow>\<^sub>a ((fst sx' + fx, snd sx'), unliftC cc')\<close>
    using assms
    apply clarsimp
    apply (frule double_aopstep_implies_fst_opstep, fast, fast, simp)
    done
  moreover have right_step:
    \<open>((fst sy + fy, snd sy), c) \<midarrow>\<alpha>\<rightarrow>\<^sub>a ((fst sy' + fy, snd sy'), unliftC cc')\<close>
    using assms
    apply clarsimp
    apply (frule double_aopstep_implies_snd_opstep, fast, fast, simp)
    done
  ultimately show ?thesis
    using assms
    by fastforce
qed

lemma eastep_implies_double_step:
  fixes sscc :: \<open>(('l::pre_perm_alg \<times> 'l) \<times> ('s \<times> 's)) \<times> _ comm\<close>
    and \<rho> :: \<open>unit act eact list\<close>
  assumes
    \<open>sscc \<midarrow>RR, FF, \<alpha>\<rightarrow>\<^sub>e\<^sub>a msscc'\<close>
    \<open>sscc = (exch4 (sx, sy), liftC c)\<close>
    \<open>msscc' = ((exch4 (sx', sy')), cc')\<close>
    \<open>(=) \<le> CC\<close>
  shows
    \<open>((sx, c), (sy, c)) =RR, FF, CC, ([\<alpha>], [\<alpha>])\<Rightarrow> ((sx', unliftC cc'), (sy', unliftC cc'))\<close>
  using assms
  apply -
  apply (erule estepE)
   apply clarsimp
   apply blast
  apply clarsimp
  apply (rename_tac lxx lyy sxx syy fx fy lxx' lyy' sxx' syy')
  apply (clarsimp simp add: exch4_def split: prod.splits)
  apply (frule_tac fx=fx and fy=fy and c=c and sx=sx and sy=sy and sx'=sx' and sy'=sy' and
      cc'=cc' and RR=RR and FF=FF in aopstep_implies_double_step)
           apply (simp; fail)+
  done

lemma esteps_implies_weak_double_steps:
  fixes sscc :: \<open>(('l::pre_perm_alg \<times> 'l) \<times> ('s \<times> 's)) \<times> _ comm\<close>
  shows
  \<open>sscc \<midarrow>RR, FF, \<rho>\<rightarrow>\<^sub>e\<^sub>a\<^sup>* msscc' \<Longrightarrow>
    sscc = (exch4 (sx, sy), liftC c) \<Longrightarrow>
    msscc' = ((exch4 (sx', sy')), cc') \<Longrightarrow>
    (=) \<le> CC \<Longrightarrow>
    ((sx, c), (sy, c)) =RR, FF, CC, (\<rho>, \<rho>)\<Rightarrow>\<^sup>* ((sx', unliftC cc'), (sy', unliftC cc'))\<close>
  apply (induct RR FF \<rho> sscc msscc' arbitrary: sx sy c cc' sx' sy' rule: easteps_induct[consumes 1])
    apply force
   apply force
  apply clarsimp
  apply (rule dsteps_step[of _ _ _ \<open>[\<alpha>]\<close> \<open>[\<alpha>]\<close> for \<alpha>, simplified])
  oops
(*
   apply (frule estep_implies_double_step)
      apply (clarsimp simp add: exch4_def split: prod.splits, fast)
     apply (clarsimp simp add: exch4_def split: prod.splits, fast)
    apply assumption
   apply fast
  apply (drule_tac x=\<open>unliftC c'\<close> in spec)
  apply clarsimp
  apply (frule eaopstep_preserves_reflclC)
   apply (simp; fail)
  apply clarsimp
  done
*)


subsubsection \<open> from double-step to aopstep \<close>

lemma restr_dstep_then_aopstep:
  fixes sx :: \<open>'l::pre_perm_alg \<times> 's\<close>
  assumes
    \<open>(((sx, cx), sy, cy) =RR, FF, CC, ([Loc \<alpha>], [Loc \<alpha>])\<Rightarrow> ((sx', cx'), sy', cy'))\<close>
    \<open>basic_tau_reducts sx cx = basic_tau_reducts sy cy\<close>
    \<open>(=) \<le> CC\<close>
  shows
    \<open>basic_tau_reducts sx' cx' = basic_tau_reducts sy' cy' \<and>
      (\<exists>fx fy.
        FF ((fx, fy), snd sx, snd sy) \<and>
        fst sx ## fx \<and>
        fst sy ## fy \<and>
        FF ((fx, fy), snd sx', snd sy') \<and>
        fst sx' ## fx \<and>
        fst sy' ## fy \<and>
        (((fst sx + fx, fst sy + fy), snd sx, snd sy), liftC' cx cy)
          \<midarrow>\<alpha>\<rightarrow>\<^sub>a (((fst sx' + fx, fst sy' + fy), snd sx', snd sy'), liftC' cx' cy'))\<close>
  using assms
  apply (elim dstep.cases, blast, blast, blast)
  apply clarsimp
  apply (rename_tac sxl sxs sxl' sxs')
  apply (frule_tac sx=\<open>(_+fx,_)\<close> and sy=\<open>(_+fy,_)\<close> in aopstep_then_pair_aopstep)
  sorry

lemma esteps_implies_weak_double_steps:
  fixes sscc :: \<open>(('l::pre_perm_alg \<times> 'l) \<times> ('s \<times> 's)) \<times> _ comm\<close>
  shows
  \<open>sscc \<midarrow>RR, FF, \<rho>\<rightarrow>\<^sub>e\<^sub>a\<^sup>* msscc' \<Longrightarrow>
    sscc = (exch4 (sx, sy), liftC c) \<Longrightarrow>
    msscc' = ((exch4 (sx', sy')), cc') \<Longrightarrow>
    (=) \<le> CC \<Longrightarrow>
    ((sx, c), (sy, c)) =RR, FF, CC, (\<rho>, \<rho>)\<Rightarrow>\<^sup>* ((sx', unliftC cc'), (sy', unliftC cc'))\<close>
  apply (induct RR FF \<rho> sscc msscc' arbitrary: sx sy c cc' sx' sy' rule: easteps_induct[consumes 1])
    apply force
   apply force
  apply clarsimp
  apply (rule dsteps_step[of _ _ _ \<open>[\<alpha>]\<close> \<open>[\<alpha>]\<close> for \<alpha>, simplified])
  oops
(*
   apply (frule estep_implies_double_step)
      apply (clarsimp simp add: exch4_def split: prod.splits, fast)
     apply (clarsimp simp add: exch4_def split: prod.splits, fast)
    apply assumption
   apply fast
  apply (drule_tac x=\<open>unliftC c'\<close> in spec)
  apply clarsimp
  apply (frule eaopstep_preserves_reflclC)
   apply (simp; fail)
  apply clarsimp
  done
*)

(*
text \<open> Double execution aggregation lemma \<close>
theorem determ_double_exec_then_safe_state:
  fixes n :: nat
    and c :: \<open>('l::pre_perm_alg \<times> 's) comm\<close>
    and sx sy :: \<open>'l \<times> 's\<close>
    and r :: \<open>'s \<Rightarrow> 's \<Rightarrow> bool\<close>
    and F :: \<open>'l \<times> 's \<Rightarrow> bool\<close>
  assumes inductive_assms:
    \<open>safe n cc zz rr gg qq SS FF\<close>
    \<open>cc = liftC c\<close>
    \<open>zz = (exch4 (sx, sy))\<close>
    \<open>((sx, c), (sy, c)) =rr, FF, (=), (\<rho>x, \<rho>y)\<Rightarrow>\<^sup>* ((msx', c'), (msy', c'))\<close>
    \<open>length \<rho>x < n\<close>
    \<open>length \<rho>y < n\<close>
  and noninductive_assms:
    \<open>\<forall>l s. FF (l, s) \<longrightarrow> (cancellative \<times>\<^sub>P cancellative) l\<close>
    \<comment> \<open>rely_obs_safe \<oo> r\<close> \<comment> \<open> we don't need this because rr is inherently declassifying \<close>
  shows
    \<open>cx' = cy' \<and> (\<exists>sx' sy'. msx' = sx' \<and> msy' = sy' \<and> SS (exch4 (sx', sy')))\<close>
  using inductive_assms
proof (induct n arbitrary: cc zz c sx sy \<rho>x \<rho>y cx' cy')
  case 0
  then show ?case
    by (clarsimp simp add: le_fun_def)
next
  case (Suc n)

  obtain sxl sxs where sx_split: \<open>sx = (sxl, sxs)\<close>
    by fastforce
  obtain syl sys where sy_split: \<open>sy = (syl, sys)\<close>
    by fastforce

  show ?case
    using Suc.prems sx_split sy_split
    apply (clarsimp simp add: liftC_rev_iff simp del: comp_apply)
    apply (erule dsteps.cases, force)
    apply (clarsimp simp del: comp_apply)
    apply (erule dstep.cases; clarsimp)
      (* Env *)
     apply (rename_tac sxs' sys' \<gamma>\<gamma>s)
     apply (clarsimp simp add: safe_suc_iff)
     apply (drule spec2, drule mp, assumption)
     apply (drule Suc.hyps)
          apply (simp; fail)
         apply (simp; fail)
        apply (simp; fail)
       apply (simp; fail)
      apply (clarsimp simp add: pred_executions_suc_iff)
      apply (metis (no_types, lifting) ext comp_apply)
     apply (simp; fail)
      (* Local *)
    apply (rename_tac sx' c' ly' sy' \<gamma>\<gamma>s' fx fy \<tau>xs cx' \<alpha>ax lx' \<tau>ys cy' \<alpha>ay)
    apply (clarsimp simp add: safe_suc_iff)
    apply (subgoal_tac \<open>\<alpha>ay = \<alpha>ax\<close>)
     prefer 2 (* TODO: not true *)
    subgoal sorry
    apply (subgoal_tac \<open>cx' = cy'\<close>)
     prefer 2 (* TODO: not true *)
    subgoal sorry
    apply clarsimp
    apply (frule(1) double_stepI[where sxs=sxs and sys=sys])
     apply (clarsimp simp add: pred_executions_suc_iff le_fun_def sepconj_conjI)
    subgoal sorry
    apply (drule_tac x=\<open>strip_aact \<alpha>ax\<close> in spec, drule spec2, drule spec2,
        drule mp, (rule conjI; assumption))
    apply (drule mp, rule strip_aopstep, assumption)
    apply clarsimp
    apply (rename_tac lx'2 ly'2)
    apply (subgoal_tac \<open>lx'2 = lx' \<and> ly'2 = ly'\<close>)
     prefer 2
     apply (cut_tac noninductive_assms(1))
     apply (simp add: pred_Times_def)
     apply (metis cancellativeD)
    apply (clarify, simp)
    apply (drule Suc.hyps)
         apply (simp add: exch4_def; fail)
        apply (simp; fail)
       apply (simp; fail)
      apply (simp; fail)
     apply (clarsimp simp add: pred_executions_suc_iff)
     apply (drule spec2, drule spec2, drule spec2, drule spec2,
        drule mp, (rule conjI; assumption))
     apply (drule mp, rule strip_aopstep, assumption)
     apply clarsimp
     apply (rename_tac lx'2 ly'2)
     apply (subgoal_tac \<open>lx'2 = lx' \<and> ly'2 = ly'\<close>)
      prefer 2
      apply (cut_tac noninductive_assms(1))
      apply (simp add: pred_Times_def)
      apply (metis cancellativeD)
     apply (clarify, simp)
     apply (simp add: le_fun_def; fail)
    apply force
    done
qed
*)

section \<open> Synchronised and Non-leaky Traces \<close>

text \<open>
  Take... probably 5 or 6 by this point.
  Hopefully this one means what we actually want it to mean.
\<close>

datatype ('s, 'a) cfg_trace =
  CTrInit \<open>'s \<times> 's comm\<close> |
  CTrStep \<open>'s \<times> 's comm\<close> 'a \<open>('s, 'a) cfg_trace\<close>

fun curr_cfg :: \<open>('s, 'a) cfg_trace \<Rightarrow> 's \<times> 's comm\<close> where
  \<open>curr_cfg (CTrInit sc) = sc\<close>
| \<open>curr_cfg (CTrStep sc \<alpha> \<rho>) = sc\<close>

datatype crash_flag = Crashed | Running

inductive_set cfg_traces
  :: \<open>('l \<times> 's) \<times> ('l \<times> 's) comm \<Rightarrow>
      (('l \<times> 's, aact eact) cfg_trace \<times> crash_flag) set\<close>
  for sc
  where
    cfg_traces_init[intro!]:
    \<open>(CTrInit sc, Running) \<in> cfg_traces sc\<close>
  | cfg_traces_local_step[intro!]:
    \<open>(\<rho>, Running) \<in> cfg_traces sc \<Longrightarrow>
      curr_cfg \<rho> \<midarrow>\<alpha>\<rightarrow>\<^sub>a (s', c') \<Longrightarrow>
      (CTrStep (s', c') (Loc \<alpha>) \<rho>, Running) \<in> cfg_traces sc\<close>
| cfg_traces_crash[intro!]:
    \<open>(\<rho>, Running) \<in> cfg_traces sc \<Longrightarrow>
      \<exists>\<alpha> c'. curr_cfg \<rho> \<midarrow>\<alpha>\<rightarrow>\<^sub>a (Inr (), c') \<Longrightarrow>
      (\<rho>, Crashed) \<in> cfg_traces sc\<close>
| cfg_traces_env_step[intro!]:
    \<open>(\<rho>, Running) \<in> cfg_traces sc \<Longrightarrow>
      curr_cfg \<rho> = (s, c) \<Longrightarrow>
      \<comment> \<open> s' unconstrained \<close>
      (CTrStep (s', c) Env \<rho>, Running) \<in> cfg_traces sc\<close>

inductive_cases cfg_traces_initE[elim!]:
  \<open>(CTrInit sca, Running) \<in> cfg_traces scb\<close>
inductive_cases cfg_traces_locE[elim]:
  \<open>(CTrStep sc' (Loc \<alpha>) \<rho>, Running) \<in> cfg_traces sc\<close>
inductive_cases cfg_traces_crashE[elim!]:
  \<open>(\<rho>, Crashed) \<in> cfg_traces sc\<close>
inductive_cases cfg_traces_envE[elim!]:
  \<open>(CTrStep sc' Env \<rho>, Running) \<in> cfg_traces sc\<close>
*)

fun nonsync_aact :: \<open>aact \<Rightarrow> bool\<close> where
  \<open>nonsync_aact TauINdetL = False\<close>
| \<open>nonsync_aact TauINdetR = False\<close>
| \<open>nonsync_aact (PL \<alpha>) = nonsync_aact \<alpha>\<close>
| \<open>nonsync_aact (PR \<alpha>) = nonsync_aact \<alpha>\<close>
| \<open>nonsync_aact TauBasic = True\<close>
| \<open>nonsync_aact AVis = True\<close>

(*
inductive synchronised_ctr_pair
  :: \<open>('s \<times> 's \<Rightarrow> 's \<times> 's \<Rightarrow> bool) \<Rightarrow>
    ('l \<times> 's, aact eact) cfg_trace \<Rightarrow>
    ('l \<times> 's, aact eact) cfg_trace \<Rightarrow>
    bool\<close>
  where
  sctrp_nil[intro!]:
  \<open>synchronised_ctr_pair R (CTrInit sx) (CTrInit sy)\<close>
| sctrp_loc_left[intro]:
  \<open>nonsync_aact \<alpha> \<Longrightarrow>
    synchronised_ctr_pair R \<rho>x \<rho>y \<Longrightarrow>
    synchronised_ctr_pair R (CTrStep sx' (Loc \<alpha>) \<rho>x) \<rho>y\<close>
| sctrp_loc_right[intro]:
  \<open>nonsync_aact \<alpha> \<Longrightarrow>
    synchronised_ctr_pair R \<rho>x \<rho>y \<Longrightarrow>
    synchronised_ctr_pair R \<rho>x (CTrStep sy' (Loc \<alpha>) \<rho>y)\<close>
| sctrp_loc_sync[intro]:
  \<open>\<not> nonsync_aact \<alpha> \<Longrightarrow>
    synchronised_ctr_pair R \<rho>x \<rho>y \<Longrightarrow>
    synchronised_ctr_pair R
      (CTrStep sx' (Loc \<alpha>) \<rho>x) (CTrStep sy' (Loc \<alpha>) \<rho>y)\<close>
| sctrp_env[intro!]:
  \<open>R (snd (fst (curr_cfg \<rho>x)), snd (fst (curr_cfg \<rho>y)))
      (snd (fst sx'), (snd (fst sy'))) \<Longrightarrow>
    synchronised_ctr_pair R \<rho>x \<rho>y \<Longrightarrow>
    synchronised_ctr_pair R (CTrStep sx' Env \<rho>x) (CTrStep sy' Env \<rho>y)\<close>

inductive_cases sctr_pair_init_leftE[elim!]:
  \<open>synchronised_ctr_pair R (CTrInit sx) \<delta>y\<close>
inductive_cases sctr_pair_init_rightE[elim!]:
  \<open>synchronised_ctr_pair R \<delta>x (CTrInit sy)\<close>
inductive_cases sctr_pair_step_loc_leftE[elim]:
  \<open>synchronised_ctr_pair R (CTrStep sx' (Loc \<alpha>) \<delta>x) \<delta>y\<close>
inductive_cases sctr_pair_step_loc_rightE[elim]:
  \<open>synchronised_ctr_pair R \<delta>x (CTrStep sy' (Loc \<alpha>) \<delta>y)\<close>
inductive_cases sctr_pair_step_env_leftE[elim]:
  \<open>synchronised_ctr_pair R (CTrStep sx' Env \<delta>x) \<delta>y\<close>
inductive_cases sctr_pair_step_env_rightE[elim]:
  \<open>synchronised_ctr_pair R \<delta>x (CTrStep sy' Env \<delta>y)\<close>


inductive leakfree_ctr_pair
  :: \<open>(('l \<times> 's) \<times> ('l \<times> 's) \<Rightarrow> bool) \<Rightarrow>
      ('l \<times> 's, aact eact) cfg_trace \<Rightarrow>
      ('l \<times> 's, aact eact) cfg_trace \<Rightarrow>
      bool\<close>
  where
  lctrp_nil[intro!]:
  \<open>S (fst scx, fst scy) \<Longrightarrow> leakfree_ctr_pair S (CTrInit scx) (CTrInit scy)\<close>
| lctrp_loc_left_btau[intro]:
  \<open>basic_tau_aact \<alpha> \<Longrightarrow>
    S (fst scx', fst (curr_cfg \<rho>y)) \<Longrightarrow>
    leakfree_ctr_pair S \<rho>x \<rho>y \<Longrightarrow>
    leakfree_ctr_pair S (CTrStep scx' (Loc \<alpha>) \<rho>x) \<rho>y\<close>
| lctrp_loc_right_btau[intro]:
  \<open>basic_tau_aact \<alpha> \<Longrightarrow>
    S (fst (curr_cfg \<rho>x), fst scy') \<Longrightarrow>
    leakfree_ctr_pair S \<rho>x \<rho>y \<Longrightarrow>
    leakfree_ctr_pair S \<rho>x (CTrStep scy' (Loc \<alpha>) \<rho>y)\<close>
| lctrp_loc_step_sync[intro]:
  \<open>\<not> basic_tau_aact \<alpha> \<Longrightarrow>
    leakfree_ctr_pair S \<rho>x \<rho>y \<Longrightarrow>
    leakfree_ctr_pair S
      (CTrStep sx' (Loc \<alpha>) \<rho>x)
      (CTrStep sy' (Loc \<alpha>) \<rho>y)\<close>
| lctrp_env[intro!]:
  \<open>S (fst scx', fst scy') \<Longrightarrow>
    leakfree_ctr_pair S \<rho>x \<rho>y \<Longrightarrow>
    leakfree_ctr_pair S (CTrStep scx' Env \<rho>x) (CTrStep scy' Env \<rho>y)\<close>

inductive_cases lctr_pair_init_leftE[elim!]:
  \<open>leakfree_ctr_pair R (CTrInit sx) \<delta>y\<close>
inductive_cases lctr_pair_init_rightE[elim!]:
  \<open>leakfree_ctr_pair R \<delta>x (CTrInit sy)\<close>
inductive_cases lctr_pair_step_loc_leftE[elim]:
  \<open>leakfree_ctr_pair R (CTrStep sx' (Loc \<alpha>) \<delta>x) \<delta>y\<close>
inductive_cases lctr_pair_step_loc_rightE[elim]:
  \<open>leakfree_ctr_pair R \<delta>x (CTrStep sy' (Loc \<alpha>) \<delta>y)\<close>
inductive_cases lctr_pair_step_env_leftE[elim]:
  \<open>leakfree_ctr_pair R (CTrStep sx' Env \<delta>x) \<delta>y\<close>
inductive_cases lctr_pair_step_env_rightE[elim]:
  \<open>leakfree_ctr_pair R \<delta>x (CTrStep sy' Env \<delta>y)\<close>


definition
  \<open>secure_ctr_pair R S \<rho>kx \<rho>ky \<equiv>
    synchronised_ctr_pair R (fst \<rho>kx) (fst \<rho>ky) \<longrightarrow>
      leakfree_ctr_pair S (fst \<rho>kx) (fst \<rho>ky) \<and> snd \<rho>kx = snd \<rho>ky\<close>


section \<open> Security \<close>

lemma safe_ensures_exec_no_crash:
  \<open>safe n c z r g q S F \<Longrightarrow>
    z = s \<Longrightarrow>
    (s, c) \<midarrow>r, F, \<rho>\<rightarrow>\<^sub>e\<^sup>* (ms', c') \<Longrightarrow>
    length \<rho> \<le> n \<Longrightarrow>
    \<forall>f s. F (f,s) \<longrightarrow> cancellative f \<Longrightarrow>
    \<exists>s'. ms' = s'\<close>
  apply (induct arbitrary: s \<rho> rule: safe.inducts)
   apply force
  apply clarsimp
  apply (erule esteps.cases)
    apply force
   apply (clarsimp, blast)
  apply clarsimp
  apply (erule estepE)
   apply force
  apply clarsimp
  apply (drule meta_spec2, drule meta_spec2, drule meta_mp, assumption,
      drule meta_mp, assumption, drule meta_mp, assumption)
  apply clarsimp
  apply (metis cancellativeD)
  done

(* TODO: probably could be moved. *)
text \<open>
  A simple lemma: execution to any state means the state predicate holds on that state.
\<close>
lemma safe_ensures_exec_always_state_pred:
  \<open>safe n c z R G q S F \<Longrightarrow>
    z = s \<Longrightarrow>
    (s, c) \<midarrow>R, F, \<rho>\<rightarrow>\<^sub>e\<^sup>* (s', c') \<Longrightarrow>
    length \<rho> \<le> n \<Longrightarrow>
    \<forall>f s. F (f,s) \<longrightarrow> cancellative f \<Longrightarrow>
    \<forall>s s' l. R s s' \<longrightarrow> S (l,s) \<longrightarrow> S (l,s') \<Longrightarrow>
    S s \<Longrightarrow>
    S s'\<close>
  apply (induct arbitrary: s \<rho> rule: safe.inducts)
   apply force
  apply clarsimp
  apply (erule esteps.cases)
    apply force
   apply force
  apply clarsimp
  apply (rename_tac la' sa' la'' sa'' ca' \<rho>)
  apply (erule estepE)
   apply force
  apply clarsimp
  apply (drule meta_spec2, drule meta_spec2, drule meta_mp, assumption,
      drule meta_mp, assumption, drule meta_mp, assumption)
  apply clarsimp
  apply (subgoal_tac \<open>la'' = hl'\<close>)
   prefer 2
   apply (metis cancellativeD)
  apply clarsimp
  done

text \<open> Note the reversal. \<close>
fun cfgtrace_to_trace :: \<open>('s, 'a) cfg_trace \<Rightarrow> 'a list\<close> where
  \<open>cfgtrace_to_trace (CTrInit s) = []\<close>
| \<open>cfgtrace_to_trace (CTrStep s' \<alpha> \<rho>) = cfgtrace_to_trace \<rho> @ [\<alpha>]\<close>


text \<open> The important lemma for proving info-flow security. \<close>
lemma determ_secure_traces_implies_ex_double_exec:
  fixes sx sy :: \<open>'l::pre_perm_alg \<times> 's\<close>
    and S :: \<open>('l \<times> 'l) \<times> ('s \<times> 's) \<Rightarrow> bool\<close>
    and F :: \<open>('l \<times> 'l) \<times> ('s \<times> 's) \<Rightarrow> bool\<close>
    and R :: \<open>'s \<times> 's \<Rightarrow> 's \<times> 's \<Rightarrow> bool\<close>
  assumes
    \<open>\<forall>\<rho> mllss' cc'.
      ((llss, liftC' cx cy) \<midarrow>R, F, \<rho>\<rightarrow>\<^sub>e\<^sub>a\<^sup>* (mllss', cc')) \<longrightarrow>
      (\<exists>llss'. mllss' = llss' \<and> S llss')\<close>
    \<open>S llss\<close>
    \<open>(S \<^emph>\<and> F) \<circ> exch4 \<le> sec_head_determ c\<close>
    \<open>llss = exch4 (sx, sy)\<close>
    and
    \<comment> \<open>\<forall>f s. F (f,s) \<longrightarrow> cancellative f\<close>
    \<open>\<forall>s s' l. R s s' \<longrightarrow> S (l,s) \<longrightarrow> S (l,s')\<close>
  shows
    \<open>\<forall>fx fy.
      F ((fx, fy), (snd sx, snd sy)) \<longrightarrow>
      fst sx ## fx \<longrightarrow>
      fst sy ## fy \<longrightarrow>
      (\<delta>, Running) \<in> cfg_traces ((fst sx + fx, snd sx), cx) \<longrightarrow>
      (\<forall>\<rho>k'.
        \<rho>k' \<in> cfg_traces ((fst sy + fy, snd sy), cy) \<longrightarrow>
        secure_ctr_pair R ((S \<^emph>\<and> F) \<circ> exch4) (\<delta>, Running) \<rho>k')\<close>
proof -
  {
    fix fx fy \<delta>y ky k
    assume assms2:
      \<open>(\<delta>, k) \<in> cfg_traces ((fst sx + fx, snd sx), cx)\<close>
      \<open>k =  Running\<close>
      \<open>F ((fx, fy), snd sx, snd sy)\<close>
      \<open>fst sx ## fx\<close>
      \<open>fst sy ## fy\<close>
      \<open>(\<delta>y, ky) \<in> cfg_traces ((fst sy + fy, snd sy), cy)\<close>
    then have \<open>secure_ctr_pair R (S \<^emph>\<and> F \<circ> exch4) (\<delta>, Running) (\<delta>y, ky)\<close>
      using assms
      apply -
      apply (induct rule: cfg_traces.induct)
         apply (clarsimp simp add: secure_ctr_pair_def)
         apply (case_tac ky)
          apply clarsimp
          apply (erule sctr_pair_init_leftE)
           apply clarsimp

      sorry
  } then show ?thesis
    by simp
qed
*)


section \<open> Double Step (Attempt 2) \<close>

subsection \<open> Double Step \<close>

subsubsection \<open> Conformant Double Step \<close>

inductive dstep_conf
  :: \<open>('s \<times> 's \<Rightarrow> 's \<times> 's \<Rightarrow> bool) \<Rightarrow>
        (('l::pre_perm_alg \<times> 'l) \<times> ('s \<times> 's) \<Rightarrow> bool) \<Rightarrow>
      _ eact list \<times> _ eact list \<Rightarrow>
      (('l \<times> 's) \<times> ('l \<times> 's) comm) \<times> (('l \<times> 's) \<times> ('l \<times> 's) comm) \<Rightarrow>
      (('l \<times> 's) \<times> ('l \<times> 's) comm) \<times> (('l \<times> 's) \<times> ('l \<times> 's) comm) \<Rightarrow>
      bool\<close>
  where
  dstep_conf_env[intro!]:
    \<open>R (snd sx, snd sy) (snd sx', snd sy') \<Longrightarrow>
      fst sx' = fst sx \<Longrightarrow>
      fst sy' = fst sy \<Longrightarrow>
      dstep_conf R F ([Env], [Env])
        (((sx, kx), cx), ((sy, ky), cy))
        (((sx', kx), cx), ((sy', ky), cy))\<close>
| dstep_conf_crash_left[intro]:
  \<open>\<exists>fy. FF ((fx,fy),(snd sx, snd sy)) \<and> fst sy ## fy \<Longrightarrow>
    \<comment> \<open> left step \<close>
    fst sx ## fx \<Longrightarrow>
    ((fst sx + fx, snd sx), cx) \<midarrow>\<alpha>\<rightarrow>\<^sub>a (Inr (), cx') \<Longrightarrow>
    dstep_conf RR FF ([Loc \<alpha>], [])
      (((sx, False), cx), ((sy, ky), cy))
      (((sx, True), cx'), ((sy, ky), cy))\<close>
| dstep_conf_crash_right[intro]:
  \<open>\<exists>fx. FF ((fx,fy),(snd sx, snd sy)) \<and> fst sx ## fx \<Longrightarrow>
    \<comment> \<open> right step \<close>
    fst sy ## fy \<Longrightarrow>
    ((fst sy + fy, snd sy), cy) \<midarrow>\<alpha>\<rightarrow>\<^sub>a (Inr (), cy') \<Longrightarrow>
    dstep_conf RR FF ([], [Loc \<alpha>])
      (((sx, kx), cx), ((sy, False), cy))
      (((sx, kx), cx), ((sy, True), cy'))\<close>
| dstep_conf_step_left[intro]:
  \<open>\<exists>fy. FF ((fx,fy),(snd sx, snd sy)) \<and> fst sy ## fy \<Longrightarrow>
    nonsync_aact \<alpha> \<Longrightarrow>
    \<comment> \<open> left step \<close>
    fst sx ## fx \<Longrightarrow>
    ((fst sx + fx, snd sx), cx) \<midarrow>\<alpha>\<rightarrow>\<^sub>a ((fst sx' + fx, snd sx'), cx') \<Longrightarrow>
    dstep_conf RR FF ([Loc \<alpha>], [])
      (((sx, False), cx), ((sy, ky), cy))
      (((sx', False), cx'), ((sy, ky), cy))\<close>
| dstep_conf_step_right[intro]:
  \<open>\<exists>fx. FF ((fx,fy),(snd sx, snd sy)) \<and> fst sx ## fx \<Longrightarrow>
    nonsync_aact \<alpha> \<Longrightarrow>
    \<comment> \<open> right step \<close>
    fst sy ## fy \<Longrightarrow>
    ((fst sy + fy, snd sy), cy) \<midarrow>\<alpha>\<rightarrow>\<^sub>a ((fst sy' + fy, snd sy'), cy') \<Longrightarrow>
    dstep_conf RR FF ([], [Loc \<alpha>])
      (((sx, kx), cx), ((sy, False), cy))
      (((sx, kx), cx), ((sy', False), cy'))\<close>
| dstep_conf_local[intro]:
  \<open>FF ((fx,fy),(snd sx, snd sy)) \<Longrightarrow>
    \<not> nonsync_aact \<alpha> \<Longrightarrow>
    \<comment> \<open> left steps \<close>
    fst sx ## fx \<Longrightarrow>
    ((fst sx + fx, snd sx), cx) \<midarrow>\<alpha>\<rightarrow>\<^sub>a ((fst sx' + fx, snd sx'), cx') \<Longrightarrow>
    \<comment> \<open> right steps \<close>
    fst sx ## fx \<Longrightarrow>
    ((fst sy + fy, snd sy), cy) \<midarrow>\<alpha>\<rightarrow>\<^sub>a ((fst sy' + fy, snd sy'), cy') \<Longrightarrow>
    dstep_conf RR FF ([Loc \<alpha>], [Loc \<alpha>])
      (((sx, False), cx), ((sy, False), cy))
      (((sx', False), cx'), ((sy', False), cy'))\<close>

inductive_cases dstep_conf_nilLE[elim!]: \<open>dstep_conf RR FF ([], Y) ss zz'\<close>
inductive_cases dstep_conf_nilRE[elim!]: \<open>dstep_conf RR FF (X, []) ss zz'\<close>
inductive_cases dstep_conf_EnvXE[elim!]: \<open>dstep_conf RR FF (Env#\<rho>x, X) ss zz'\<close>
inductive_cases dstep_conf_XEnvE[elim!]: \<open>dstep_conf RR FF (X, Env#\<rho>y) ss zz'\<close>
inductive_cases dstep_conf_LocXE[elim]: \<open>dstep_conf RR FF (Loc \<alpha>x#\<rho>x, X) ss zz'\<close>
inductive_cases dstep_conf_XLocE[elim]: \<open>dstep_conf RR FF (X, Loc \<alpha>y#\<rho>y) ss zz'\<close>

abbreviation dstep_conf_pretty :: \<open>_ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> bool\<close>
  (\<open>_ =_, _, _\<Rightarrow>\<^sub>\<C> _\<close> [50, 0, 0, 0, 50])
  where
    \<open>ss =R, F, \<rho>xy\<Rightarrow>\<^sub>\<C> ss' \<equiv> dstep_conf R F \<rho>xy ss ss'\<close>


subsubsection \<open> Secure Double Step \<close>

inductive dstep_secure
  :: \<open>('s \<times> 's \<Rightarrow> 's \<times> 's \<Rightarrow> bool) \<Rightarrow>
        (('l::pre_perm_alg \<times> 'l) \<times> ('s \<times> 's) \<Rightarrow> bool) \<Rightarrow>
      _ eact list \<times> _ eact list \<Rightarrow>
      (('l \<times> 's) \<times> ('l \<times> 's) comm) \<times> (('l \<times> 's) \<times> ('l \<times> 's) comm) \<Rightarrow>
      (('l \<times> 's) \<times> ('l \<times> 's) comm) \<times> (('l \<times> 's) \<times> ('l \<times> 's) comm) \<Rightarrow>
      bool\<close>
  where
    dstep_secure_env[intro!]:
    \<open>R (snd sx, snd sy) (snd sx', snd sy') \<Longrightarrow>
      fst sx' = fst sx \<Longrightarrow>
      fst sy' = fst sy \<Longrightarrow>
      dstep_secure R F ([Env], [Env])
        (((sx, kx), cx), ((sy, ky), cy))
        (((sx', kx), cx), ((sy', ky), cy))\<close>
  | dstep_secure_crash[intro!]:
    \<comment> \<open> one process crashing when the other doesn't is a security failure. \<close>
    \<open>FF ((fx,fy),(snd sx, snd sy)) \<Longrightarrow>
    \<comment> \<open> left step \<close>
    fst sx ## fx \<Longrightarrow>
    ((fst sx + fx, snd sx), cx) \<midarrow>\<alpha>\<rightarrow>\<^sub>a (Inr (), cx') \<Longrightarrow>
    \<comment> \<open> right step \<close>
    fst sx ## fx \<Longrightarrow>
    ((fst sy + fy, snd sy), cy) \<midarrow>\<alpha>\<rightarrow>\<^sub>a (Inr (), cy') \<Longrightarrow>
    dstep_secure RR FF ([Loc \<alpha>], [Loc \<alpha>])
      (((sx, False), cx), ((sy, False), cy))
      (((sx, True), cx'), ((sy, True), cy'))\<close>
  | dstep_secure_btau_left[intro]:
    \<comment> \<open> a process may left-step if it's a basic tau move. \<close>
    \<open>\<exists>fy. FF ((fx,fy),(snd sx, snd sy)) \<and> fst sy ## fy \<Longrightarrow>
    basic_tau_aact \<alpha> \<Longrightarrow>
    \<comment> \<open> left step \<close>
    fst sx ## fx \<Longrightarrow>
    ((fst sx + fx, snd sx), cx) \<midarrow>\<alpha>\<rightarrow>\<^sub>a ((fst sx' + fx, snd sx'), cx') \<Longrightarrow>
    dstep_secure RR FF ([Loc \<alpha>], [])
      (((sx, False), cx), ((sy, ky), cy))
      (((sx', False), cx), ((sy, ky), cy'))\<close>
  | dstep_secure_btau_right[intro]:
    \<comment> \<open> a process may right-step if it's a basic tau move. \<close>
    \<open>\<exists>fx. FF ((fx,fy),(snd sx, snd sy)) \<and> fst sx ## fx \<Longrightarrow>
    basic_tau_aact \<alpha> \<Longrightarrow>
    \<comment> \<open> right step \<close>
    fst sy ## fy \<Longrightarrow>
    ((fst sy + fy, snd sy), cy) \<midarrow>\<alpha>\<rightarrow>\<^sub>a ((fst sy' + fy, snd sy'), cy') \<Longrightarrow>
    dstep_secure RR FF ([], [Loc \<alpha>])
      (((sx, kx), cx), ((sy, False), cy))
      (((sx, kx), cx), ((sy', False), cy'))\<close>
  | dstep_secure_local[intro]:
    \<comment> \<open> all other steps must be synchronised to be secure. \<close>
    \<open>FF ((fx,fy),(snd sx, snd sy)) \<Longrightarrow>
    \<not> basic_tau_aact \<alpha> \<Longrightarrow>
    \<comment> \<open> left steps \<close>
    fst sx ## fx \<Longrightarrow>
    ((fst sx + fx, snd sx), cx) \<midarrow>\<alpha>\<rightarrow>\<^sub>a ((fst sx' + fx, snd sx'), cx') \<Longrightarrow>
    \<comment> \<open> right steps \<close>
    fst sx ## fx \<Longrightarrow>
    ((fst sy + fy, snd sy), cy) \<midarrow>\<alpha>\<rightarrow>\<^sub>a ((fst sy' + fy, snd sy'), cy') \<Longrightarrow>
    dstep_secure RR FF ([Loc \<alpha>], [Loc \<alpha>])
      (((sx, False), cx), ((sy, False), cy))
      (((sx', False), cx'), ((sy', False), cy'))\<close>

inductive_cases dstep_secure_nilLE[elim!]: \<open>dstep_secure RR FF ([], Y) ss zz'\<close>
inductive_cases dstep_secure_nilRE[elim!]: \<open>dstep_secure RR FF (X, []) ss zz'\<close>
inductive_cases dstep_secure_EnvXE[elim!]: \<open>dstep_secure RR FF (Env#\<rho>x, X) ss zz'\<close>
inductive_cases dstep_secure_XEnvE[elim!]: \<open>dstep_secure RR FF (X, Env#\<rho>y) ss zz'\<close>
inductive_cases dstep_secure_LocXE[elim]: \<open>dstep_secure RR FF (Loc \<alpha>x#\<rho>x, X) ss zz'\<close>
inductive_cases dstep_secure_XLocE[elim]: \<open>dstep_secure RR FF (X, Loc \<alpha>y#\<rho>y) ss zz'\<close>

abbreviation dstep_secure_pretty :: \<open>_ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> bool\<close>
  (\<open>_ =_, _, _\<Rightarrow>\<^sub>\<S> _\<close> [50, 0, 0, 0, 50])
  where
    \<open>ss =R, F, \<rho>xy\<Rightarrow>\<^sub>\<S> ss' \<equiv> dstep_secure R F \<rho>xy ss ss'\<close>


subsubsection \<open> Exact Double Step \<close>

inductive dstep_exact
  :: \<open>('s \<times> 's \<Rightarrow> 's \<times> 's \<Rightarrow> bool) \<Rightarrow>
        (('l::pre_perm_alg \<times> 'l) \<times> ('s \<times> 's) \<Rightarrow> bool) \<Rightarrow>
      _ eact list \<times> _ eact list \<Rightarrow>
      (('l \<times> 's) \<times> ('l \<times> 's) comm) \<times> (('l \<times> 's) \<times> ('l \<times> 's) comm) \<Rightarrow>
      (('l \<times> 's) \<times> ('l \<times> 's) comm) \<times> (('l \<times> 's) \<times> ('l \<times> 's) comm) \<Rightarrow>
      bool\<close>
  where
    dstep_exact_env[intro!]:
    \<open>ss = (((sx, kx), cx), ((sy, ky), cy)) \<Longrightarrow>
      ss' = (((sx', kx), cx), ((sy', ky), cy)) \<Longrightarrow>
      R (snd sx, snd sy) (snd sx', snd sy') \<Longrightarrow>
      fst sx' = fst sx \<Longrightarrow>
      fst sy' = fst sy \<Longrightarrow>
      dstep_exact R F ([Env], [Env]) ss ss'\<close>
| dstep_exact_local[intro]:
  \<comment> \<open> all other steps must be synchronised to be secure. \<close>
  \<open>FF ((fx,fy),(snd sx, snd sy)) \<Longrightarrow>
    \<comment> \<open> left steps \<close>
    fst sx ## fx \<Longrightarrow>
    ((fst sx + fx, snd sx), cx) \<midarrow>\<alpha>\<rightarrow>\<^sub>a ((fst sx' + fx, snd sx'), cx') \<Longrightarrow>
    \<comment> \<open> right steps \<close>
    fst sx ## fx \<Longrightarrow>
    ((fst sy + fy, snd sy), cy) \<midarrow>\<alpha>\<rightarrow>\<^sub>a ((fst sy' + fy, snd sy'), cy') \<Longrightarrow>
    dstep_exact RR FF ([Loc \<alpha>], [Loc \<alpha>])
      (((sx, False), cx), ((sy, False), cy))
      (((sx', False), cx'), ((sy', False), cy'))\<close>
| dstep_exact_crash[intro]:
  \<comment> \<open> all other steps must be synchronised to be secure. \<close>
  \<open>FF ((fx,fy),(snd sx, snd sy)) \<Longrightarrow>
    \<comment> \<open> left steps \<close>
    fst sx ## fx \<Longrightarrow>
    ((fst sx + fx, snd sx), cx) \<midarrow>\<alpha>\<rightarrow>\<^sub>a (Inr (), cx') \<Longrightarrow>
    \<comment> \<open> right steps \<close>
    fst sx ## fx \<Longrightarrow>
    ((fst sy + fy, snd sy), cy) \<midarrow>\<alpha>\<rightarrow>\<^sub>a (Inr (), cy') \<Longrightarrow>
    dstep_exact RR FF ([Loc \<alpha>], [Loc \<alpha>])
      (((sx, False), cx), ((sy, False), cy))
      (((sx, True), cx'), ((sy, True), cy'))\<close>

inductive_cases dstep_exact_nilLE[elim!]: \<open>dstep_exact RR FF ([], Y) ss zz'\<close>
inductive_cases dstep_exact_nilRE[elim!]: \<open>dstep_exact RR FF (X, []) ss zz'\<close>
inductive_cases dstep_exact_EnvXE[elim!]: \<open>dstep_exact RR FF (Env#\<rho>x, X) ss zz'\<close>
inductive_cases dstep_exact_XEnvE[elim!]: \<open>dstep_exact RR FF (X, Env#\<rho>y) ss zz'\<close>
inductive_cases dstep_exact_LocXE[elim]: \<open>dstep_exact RR FF (Loc \<alpha>x#\<rho>x, X) ss zz'\<close>
inductive_cases dstep_exact_XLocE[elim]: \<open>dstep_exact RR FF (X, Loc \<alpha>y#\<rho>y) ss zz'\<close>

abbreviation dstep_exact_pretty :: \<open>_ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> bool\<close>
  (\<open>_ =_, _, _\<Rightarrow>\<^sub>\<E> _\<close> [50, 0, 0, 0, 50])
  where
    \<open>ss =R, F, \<rho>xy\<Rightarrow>\<^sub>\<E> ss' \<equiv> dstep_exact R F \<rho>xy ss ss'\<close>

lemma dstep_exact_env_iff:
  \<open>ss =R, F, ([Env], [Env])\<Rightarrow>\<^sub>\<E> ss' \<longleftrightarrow>
    (\<exists>sx kx cx sy ky cy sx' sy'.
      ss = (((sx, kx), cx), ((sy, ky), cy)) \<and>
      ss' = (((sx', kx), cx), ((sy', ky), cy)) \<and>
      R (snd sx, snd sy) (snd sx', snd sy') \<and>
      fst sx' = fst sx \<and>
      fst sy' = fst sy)\<close>
  by fastforce

lemma dstep_exact_loc_iff:
  \<open>ss =R, F, ([Loc \<alpha>x], [Loc \<alpha>y])\<Rightarrow>\<^sub>\<E> ss' \<longleftrightarrow>
    \<alpha>x = \<alpha>y \<and>
    (\<exists>sx cx sy cy.
      ss = (((sx, False), cx), ((sy, False), cy)) \<and>
    (\<exists>sx' kx' cx' sy' ky' cy'.
      ss' = (((sx', kx'), cx'), ((sy', ky'), cy')) \<and>
      ((\<exists>fx fy.
        \<not> kx' \<and> \<not> ky' \<and>
        ss = (((sx, False), cx), ((sy, False), cy)) \<and>
        ss' = (((sx', False), cx'), ((sy', False), cy')) \<and>
        F ((fx,fy),(snd sx, snd sy)) \<and>
        fst sx ## fx \<and>
        ((fst sx + fx, snd sx), cx) \<midarrow>\<alpha>x\<rightarrow>\<^sub>a ((fst sx' + fx, snd sx'), cx') \<and>
        fst sx ## fx \<and>
        ((fst sy + fy, snd sy), cy) \<midarrow>\<alpha>y\<rightarrow>\<^sub>a ((fst sy' + fy, snd sy'), cy')) \<or>
      (\<exists>fx fy.
        kx' \<and> ky' \<and>
        ss = (((sx, False), cx), ((sy, False), cy)) \<and>
        ss' = (((sx, True), cx'), ((sy, True), cy')) \<and>
        F ((fx,fy),(snd sx, snd sy)) \<and>
        fst sx ## fx \<and>
        ((fst sx + fx, snd sx), cx) \<midarrow>\<alpha>x\<rightarrow>\<^sub>a (Inr (), cx') \<and>
        fst sx ## fx \<and>
        ((fst sy + fy, snd sy), cy) \<midarrow>\<alpha>y\<rightarrow>\<^sub>a (Inr (), cy')))))\<close>
  by fast


subsection \<open> Double Executions \<close>

(* Note: appends to the end *)
inductive dexec
  :: \<open>(_ list \<times> _ list \<Rightarrow>
        ('s \<times> 's2 comm) \<times> ('s \<times> 's2 comm) \<Rightarrow>
        ('s \<times> 's2 comm) \<times> ('s \<times> 's2 comm) \<Rightarrow>
        bool) \<Rightarrow>
      (_ \<Rightarrow> _ \<Rightarrow> bool) \<Rightarrow>
      (_ \<Rightarrow> _ \<Rightarrow> bool) \<Rightarrow>
      _ list \<times> _ list \<Rightarrow>
      ('s \<times> 's2 comm) \<times> ('s \<times> 's2 comm) \<Rightarrow>
      ('s \<times> 's2 comm) \<times> ('s \<times> 's2 comm) \<Rightarrow>
      bool\<close>
  for step I C
  where
  dexec_nil[intro!]: \<comment> \<open> safe so long as \<open>step\<close> is never \<open>([],[])\<close> \<close>
  \<open>ss' = ss \<Longrightarrow>
    C (snd (fst ss)) (snd (snd ss)) \<Longrightarrow>
    I (fst (fst ss)) (fst (snd ss)) \<Longrightarrow>
    dexec step I C ([], []) ss ss'\<close>
| dexec_step[intro]:
  \<open>dexec step I C (\<rho>x, \<rho>y) ss ss' \<Longrightarrow>
    step (\<rho>x', \<rho>y') ss' ss'' \<Longrightarrow>
    C (snd (fst ss')) (snd (snd ss')) \<Longrightarrow>
    I (fst (fst ss')) (fst (snd ss')) \<Longrightarrow>
    dexec step I C (\<rho>x @ \<rho>x', \<rho>y @ \<rho>y') ss ss''\<close>

inductive_cases dexec_nilE[elim!]:
  \<open>dexec step L C ([], []) ss ss'\<close>
inductive_cases dexec_cons_leftE[elim]:
  \<open>dexec step L C (\<alpha>x # \<rho>x, \<rho>y) ss ss'\<close>
inductive_cases dexec_cons_rightE[elim]:
  \<open>dexec step L C (\<rho>x, \<alpha>y # \<rho>y) ss ss'\<close>

lemmas dexec_doublestepI[intro] =
  dexec_step[where \<rho>x=\<open>[\<alpha>x]\<close> and \<rho>y=\<open>[\<alpha>y]\<close> for \<alpha>x \<alpha>y, simplified]
lemmas dexec_step_leftI[intro] =
  dexec_step[where \<rho>x=\<open>[\<alpha>x]\<close> and \<rho>y=\<open>[]\<close> for \<alpha>x, simplified]
lemmas dexec_step_rightI[intro] =
  dexec_step[where \<rho>x=\<open>[]\<close> and \<rho>y=\<open>[\<alpha>y]\<close> for \<alpha>y, simplified]


abbreviation dexec_pretty :: \<open>_ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> bool\<close>
  (\<open>_ =_, _, _, _\<Rightarrow>\<^sup>* _\<close> [50, 0, 0, 0, 0, 50])
  where
    \<open>ss =step, L, C, \<rho>xy\<Rightarrow>\<^sup>* ss' \<equiv> dexec step L C \<rho>xy ss ss'\<close>


definition \<open>secstate_bridge I \<equiv> \<lambda>(sx, kx) (sy, ky). I (exch4 (sx, sy))\<close>

abbreviation dexec_conf :: \<open>_ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> bool\<close>
  (\<open>_ =_, _, _\<Rightarrow>\<^sub>\<C>\<^sup>* _\<close> [50, 0, 0, 0, 50])
  where
    \<open>ss =R, F, \<rho>xy\<Rightarrow>\<^sub>\<C>\<^sup>* ss' \<equiv> dexec (dstep_conf R F) \<top> \<top> \<rho>xy ss ss'\<close>

lemmas dexec_conf_induct =
  dexec.inducts[of \<open>dstep_conf R F\<close> \<top> \<top> for R F, consumes 1, case_names Nil Append]

abbreviation dexec_sync :: \<open>_ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> bool\<close>
  (\<open>_ =_, _, _, _\<Rightarrow>\<^sub>\<S>\<^sup>* _\<close> [50, 0, 0, 0, 0, 50])
  where
    \<open>ss =R, F, I, \<rho>xy\<Rightarrow>\<^sub>\<S>\<^sup>* ss' \<equiv> dexec (dstep_secure R F) (secstate_bridge I) \<top> \<rho>xy ss ss'\<close>

lemmas dexec_sync_induct = dexec.inducts[of \<open>dstep_secure R F\<close> \<top> \<top> for R F, consumes 1]

abbreviation dexec_exact :: \<open>_ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> bool\<close>
  (\<open>_ =_, _, _\<Rightarrow>\<^sub>\<E>\<^sup>* _\<close> [50, 0, 0, 0, 50])
  where
    \<open>ss =R, F, \<rho>xy\<Rightarrow>\<^sub>\<E>\<^sup>* ss' \<equiv> dexec (dstep_exact R F) \<top> (=) \<rho>xy ss ss'\<close>

lemmas dexec_exact_step_env =
  dexec_step[where step=\<open>dstep_exact R F\<close> for R F, OF _ dstep_exact_env, simplified]
lemmas dexec_exact_step_crash =
  dexec_step[where step=\<open>dstep_exact R F\<close> for R F, OF _ dstep_exact_crash, simplified]
lemmas dexec_exact_step_local =
  dexec_step[where step=\<open>dstep_exact R F\<close> for R F, OF _ dstep_exact_local, simplified]

lemmas dexec_exact_induct = dexec.inducts[of \<open>dstep_exact R F\<close> \<top> \<open>(=)\<close> for R F, consumes 1]

lemma append_eq_append_singleton_right_conv:
  \<open>xs1 @ xs2 = ys @ [y] \<longleftrightarrow>
    (xs1 = ys @ [] \<and> xs2 = [y]) \<or>
    (xs1 = ys @ [y] \<and> xs2 = []) \<or>
    (\<exists>us. xs1 @ us = ys \<and> xs2 = us @ [y])\<close>
  by (force simp add: append_eq_append_conv2 append_eq_Cons_conv conj_disj_distribL)

lemma dexec_exact_left_rconsD:
  \<open>dexec step I C \<rho>\<rho> ss ss'' \<Longrightarrow>
    step = dstep_exact R F \<Longrightarrow>
    \<rho>\<rho> = (\<rho>x @ [\<alpha>], \<rho>y') \<Longrightarrow>
    (\<exists>\<rho>y \<alpha>y sx' cx' sy' cy'.
      \<rho>y' = \<rho>y @ [\<alpha>] \<and>
      dexec step I C (\<rho>x, \<rho>y) ss ((sx', cx'), (sy', cy')) \<and>
      dstep_exact R F ([\<alpha>], [\<alpha>]) ((sx', cx'), (sy', cy')) ss'' \<and>
      I sx' sy' \<and>
      C cx' cy')\<close>
  apply (erule dexec.cases)
   apply blast
  apply (clarsimp simp add: append_eq_append_singleton_right_conv del: disjCI)
  apply (clarsimp simp add: conj_disj_distribR ex_disj_distrib del: disjCI)
  apply (erule dstep_exact.cases)
    apply (clarsimp simp add: dstep_exact_env_iff, metis)
   apply (clarsimp simp add: dstep_exact_loc_iff, metis)
  apply (clarsimp simp add: dstep_exact_loc_iff, metis)
  done

lemma dexec_exact_left_rcons_iff:
  \<open>dexec (dstep_exact R F) I C (\<rho>x @ [\<alpha>], \<rho>y') ss ss'' \<longleftrightarrow>
    (\<exists>\<rho>y \<alpha>y sx' cx' sy' cy'.
      \<rho>y' = \<rho>y @ [\<alpha>] \<and>
      dexec (dstep_exact R F) I C (\<rho>x, \<rho>y) ss ((sx', cx'), (sy', cy')) \<and>
      dstep_exact R F ([\<alpha>], [\<alpha>]) ((sx', cx'), (sy', cy')) ss'' \<and>
      I sx' sy' \<and>
      C cx' cy')\<close>
  apply (rule iffI)
   apply (drule dexec_exact_left_rconsD; blast)
  apply (clarsimp, rule dexec_step, assumption, assumption, force, force)
  done


section \<open> Security Theorem \<close>

lemma dexec_conf_left_crash_preserved_fwd:
  \<open>ss =R, F, \<rho>\<rho>\<Rightarrow>\<^sub>\<C>\<^sup>* ss' \<Longrightarrow>
    snd (fst (fst ss)) \<Longrightarrow>
    snd (fst (fst ss'))\<close>
  by (induct rule: dexec_conf_induct) (force elim: dstep_conf.cases)+

lemma dexec_conf_right_crash_preserved_fwd:
  \<open>ss =R, F, \<rho>\<rho>\<Rightarrow>\<^sub>\<C>\<^sup>* ss' \<Longrightarrow>
    snd (fst (snd ss)) \<Longrightarrow>
    snd (fst (snd ss'))\<close>
  by (induct rule: dexec_conf_induct) (force elim: dstep_conf.cases)+


lemma empty_rely_no_env_estep:
  \<open>sc \<midarrow>F, \<bottom>, \<alpha>e\<rightarrow>\<^sub>e\<^sub>a sc' \<Longrightarrow>
    \<exists>\<alpha>. \<alpha>\<^sub>e = Loc \<alpha>\<close>
  by (cases \<alpha>e) force+

lemma empty_rely_no_env_esteps:
  \<open>sc \<midarrow>R, F, \<rho>e\<rightarrow>\<^sub>e\<^sub>a\<^sup>* sc' \<Longrightarrow>
    R = \<bottom> \<Longrightarrow>
    list_all (\<lambda>\<alpha>e. \<exists>\<alpha>. \<alpha>e = Loc \<alpha>) \<rho>e\<close>
  by (induct rule: easteps_induct) force+


section \<open> Basic tau equivalence \<close>

definition sync_set
  :: \<open>('l::pre_perm_alg \<times> 's \<Rightarrow> bool) \<Rightarrow>
      ('l::pre_perm_alg \<times> 's) config \<Rightarrow>
      ('l \<times> 's) comm set\<close>
  where
    \<open>sync_set FF \<equiv> \<lambda>sc.
      {c''. \<exists>\<rho>e c' s'.
        (sc \<midarrow>\<bottom>, FF, \<rho>e\<rightarrow>\<^sub>e\<^sub>a\<^sup>* (s', c')) \<and>
        list_all (\<lambda>\<alpha>e. \<exists>\<alpha>. \<alpha>e = Loc \<alpha> \<and> basic_tau_aact \<alpha>) \<rho>e \<and>
        (\<exists>\<alpha> s''. (s', c') \<midarrow>\<alpha>\<rightarrow>\<^sub>a (s'', c'') \<and> \<not> basic_tau_aact \<alpha>)}\<close>

definition can_btau_crash
  :: \<open>('l::pre_perm_alg \<times> 's \<Rightarrow> bool) \<Rightarrow>
      ('l \<times> 's) config \<Rightarrow>
      bool\<close>
  where
    \<open>can_btau_crash F sc \<equiv>
      \<exists>\<rho>e s' c'.
        (sc \<midarrow>\<bottom>, F, \<rho>e\<rightarrow>\<^sub>e\<^sub>a\<^sup>* (s', c')) \<and>
        list_all (\<lambda>\<alpha>e. \<exists>\<alpha>. \<alpha>e = Loc \<alpha> \<and> basic_tau_aact \<alpha>) \<rho>e \<and>
        (\<exists>\<alpha> c'' f.
          F (f, snd s') \<and>
          fst s' ## f \<and>
          ((fst s' + f, snd s'), c') \<midarrow>\<alpha>\<rightarrow>\<^sub>a (Inr (), c''))\<close>

definition btau_equiv
  :: \<open>('l::pre_perm_alg \<times> 's \<Rightarrow> bool) \<Rightarrow>
        ('l::pre_perm_alg \<times> 's) config \<Rightarrow> ('l \<times> 's) config \<Rightarrow> bool\<close>
  where
    \<open>btau_equiv FF sca scb \<equiv>
      sync_set FF sca = sync_set FF scb \<and>
      can_btau_crash FF sca = can_btau_crash FF scb\<close>


lemma left_crash_and_btau_equiv_implies_right_can_btau_crash:
  fixes cx cy :: \<open>('l::pre_perm_alg \<times> 's) comm\<close>
    and lsx lsy fx fy :: 'l
    and ssx ssy :: 's
  shows
  \<open>F (fx, ssx) \<Longrightarrow>
    lsx ## fx \<Longrightarrow>
    ((lsx + fx, ssx), cx) \<midarrow>\<alpha>\<rightarrow>\<^sub>a (Inr (), cx') \<Longrightarrow>
    btau_equiv F ((lsx, ssx), cx) ((lsy, ssy), cy) \<Longrightarrow>
    can_btau_crash F ((lsy, ssy), cy)\<close>
  apply (clarsimp simp add: btau_equiv_def del: disjCI)
  apply (simp add: can_btau_crash_def[of _ \<open>((lsx, _), _)\<close>])
  apply (drule spec[of _ \<open>[]\<close>], simp)
  done

lemma right_crash_and_btau_equiv_implies_left_can_btau_crash:
  fixes cx cy :: \<open>('l::pre_perm_alg \<times> 's) comm\<close>
    and lsx lsy fx fy :: 'l
    and ssx ssy :: 's
  shows
  \<open>F (fy, ssy) \<Longrightarrow>
    lsy ## fy \<Longrightarrow>
    ((lsy + fy, ssy), cy) \<midarrow>\<alpha>\<rightarrow>\<^sub>a (Inr (), cy') \<Longrightarrow>
    btau_equiv F ((lsx, ssx), cx) ((lsy, ssy), cy) \<Longrightarrow>
    can_btau_crash F ((lsx, ssx), cx)\<close>
  apply (clarsimp simp add: btau_equiv_def del: disjCI)
  apply (simp add: can_btau_crash_def[of _ \<open>((lsy, _), _)\<close>])
  apply (drule spec[of _ \<open>[]\<close>], simp)
  done

lemma dexec_trans:
  \<open>ss' =step, L, C, \<rho>\<rho>'\<Rightarrow>\<^sup>* ss'' \<Longrightarrow>
    ss =step, L, C, \<rho>\<rho>\<Rightarrow>\<^sup>* ss' \<Longrightarrow>
    ss =step, L, C, (fst \<rho>\<rho> @ fst \<rho>\<rho>', snd \<rho>\<rho> @ snd \<rho>\<rho>')\<Rightarrow>\<^sup>* ss''\<close>
  apply (induct rule: dexec.inducts)
   apply force
  apply (clarsimp, metis append.assoc dexec_step fst_conv snd_conv)
  done


subsubsection \<open> Aopstep lemmas \<close>

lemma tau_aexec_preserves_state:
  \<open>(s, c) \<midarrow>\<rho>\<rightarrow>\<^sub>a\<^sup>* (s', c') \<Longrightarrow>
    list_all tau_aact \<rho> \<Longrightarrow>
    s' = s\<close>
  apply (induct \<rho> arbitrary: s c s' c')
   apply force
  apply clarsimp
  apply (rename_tac ls ss c ls'' ss'' c'' ls' ss' c')
  apply (metis aopstep_tau_preserves_state fst_eqD sum.sel(1))
  done

lemma btau_aexec_preserves_state:
  \<open>(s, c) \<midarrow>\<rho>\<rightarrow>\<^sub>a\<^sup>* (s', c') \<Longrightarrow>
    list_all basic_tau_aact \<rho> \<Longrightarrow>
    s' = s\<close>
  by (metis basic_tau_aact_then_tau_aact list.pred_mono_strong tau_aexec_preserves_state)

lemma tau_aopstep_state_irrelevant:
  \<comment> \<open> False because of do loops \<close>
  \<open>sc \<midarrow>\<alpha>\<rightarrow>\<^sub>a sc' \<Longrightarrow> tau_aact \<alpha> \<Longrightarrow> (sx, snd sc) \<midarrow>\<alpha>\<rightarrow>\<^sub>a (sx, snd sc')\<close>
  apply (induct \<alpha> sc sc' rule: aopstep_induct)
        apply force
       apply force
      apply force
     apply force
    apply force
   apply clarsimp
  subgoal sorry
  apply force
  oops

lemma btau_astep_preserves_nextstep:
  \<open>sc \<midarrow>\<alpha>\<rightarrow>\<^sub>a sc' \<Longrightarrow>
    sc' = (s', c') \<Longrightarrow>
    basic_tau_aact \<alpha> \<Longrightarrow>
    sc \<midarrow>\<alpha>x\<rightarrow>\<^sub>a (sx, cx) \<Longrightarrow>
    \<alpha>x \<noteq> \<alpha> \<Longrightarrow>
    \<exists>cx'. (s', c') \<midarrow>\<alpha>x\<rightarrow>\<^sub>a (sx, cx')\<close>
  apply (frule aopstep_tau_preserves_state, force)
  apply (induct \<alpha> sc sc' arbitrary: s' c' \<alpha>x sx cx rule: aopstep_induct)
        apply force
       apply fastforce
      apply fastforce
     apply clarsimp
     apply (erule disjE, force simp add: if_bool_eq_disj)
     apply (erule disjE, force simp add: if_bool_eq_disj)
     apply (erule disjE, force simp add: if_bool_eq_disj)
     apply (erule disjE, force simp add: if_bool_eq_disj)
     apply (erule disjE; clarsimp simp add: if_bool_eq_disj, metis)
    apply clarsimp
    apply (erule disjE, force)
    apply (erule disjE, force)
    apply (elim disjE exE conjE)
       apply (simp; fail)
      apply force
     apply force
    apply (simp; fail)
   apply fastforce
  apply fastforce
  done

lemma btau_aexec_preserves_nonbtau_nextstep:
  \<open>(s, c) \<midarrow>\<rho>\<rightarrow>\<^sub>a\<^sup>* (s', c') \<Longrightarrow>
    list_all basic_tau_aact \<rho> \<Longrightarrow>
    \<not> basic_tau_aact \<alpha>x \<Longrightarrow>
    (s, c) \<midarrow>\<alpha>x\<rightarrow>\<^sub>a (sx, cx) \<Longrightarrow>
    \<exists>cx'. (s', c') \<midarrow>\<alpha>x\<rightarrow>\<^sub>a (sx, cx')\<close>
  apply (induct \<rho> arbitrary: s c \<alpha>x s' c' sx cx)
   apply force
  apply (simp, metis btau_astep_preserves_nextstep)
  done

lemma aopsteps_trans:
  \<open>sc \<midarrow>\<rho>a\<rightarrow>\<^sub>a\<^sup>* sc' \<Longrightarrow>
    sc' = (s', c') \<Longrightarrow>
    (s', c') \<midarrow>\<rho>b\<rightarrow>\<^sub>a\<^sup>* sc'' \<Longrightarrow>
    sc \<midarrow>\<rho>a @ \<rho>b\<rightarrow>\<^sub>a\<^sup>* sc''\<close>
  by (induct arbitrary: \<rho>b sc'' rule: aopsteps.induct) force+

lemma basic_tau_aopstep_changes_comm:
  \<open>sc \<midarrow>\<alpha>\<rightarrow>\<^sub>a sc' \<Longrightarrow>
    sc = (s, c) \<Longrightarrow>
    sc' = (s', c') \<Longrightarrow>
    basic_tau_aact \<alpha> \<Longrightarrow>
    c' \<noteq> c\<close>
  by (induct arbitrary: s c s' c' rule: aopstep_induct) force+


subsection \<open> Basic-Tau Relations \<close>

subsubsection \<open> Basic-Tau Reduction \<close>

definition btau_reduce_comm
  :: \<open>('l \<times> 's) \<Rightarrow> ('l \<times> 's) comm \<Rightarrow> ('l \<times> 's) comm \<Rightarrow> bool\<close> (\<open>_, _ \<leadsto>\<^sub>\<tau>\<^sub>B\<^sup>* _\<close> [55,0,55] 55)
  where
    \<open>s, c \<leadsto>\<^sub>\<tau>\<^sub>B\<^sup>* c' \<equiv> \<exists>\<rho>. list_all basic_tau_aact \<rho> \<and> (s, c) \<midarrow>\<rho>\<rightarrow>\<^sub>a\<^sup>* (s, c')\<close>

lemma btau_reduce_comm_reflI[intro]:
  \<open>btau_reduce_comm s c c\<close>
  by (metis aopsteps_nil btau_reduce_comm_def fst_conv snd_conv list_all_simps(2))

lemma btau_reduce_comm_reflp:
  \<open>reflp (btau_reduce_comm s)\<close>
  by (metis reflpI btau_reduce_comm_reflI)

lemma btau_reduce_comm_transp:
  \<open>transp (btau_reduce_comm s)\<close>
  by (rule transpI, meson aopsteps_trans btau_reduce_comm_def list_all_append)

(* Note: \<open>btau_reduce_comm\<close> is not antisym, consider \<open>DO Skip;; Skip OD\<close> *)


subsubsection \<open> Basic-Tau Equiv \<close>

definition btau_equiv_trace :: \<open>aact eact list \<Rightarrow> aact eact list \<Rightarrow> bool\<close> (infix \<open>\<simeq>\<^sub>\<tau>\<^sub>B\<close> 55) where
  \<open>\<rho> \<simeq>\<^sub>\<tau>\<^sub>B \<rho>' \<equiv>
    List.filter (case_eact False (Not \<circ> basic_tau_aact)) \<rho> =
    List.filter (case_eact False (Not \<circ> basic_tau_aact)) \<rho>'\<close>

lemma nil_btau_equiv_iff[simp]:
  \<open>[] \<simeq>\<^sub>\<tau>\<^sub>B \<rho> \<longleftrightarrow> list_all (case_eact True basic_tau_aact) \<rho>\<close>
  by (induct \<rho>) (simp add: btau_equiv_trace_def split: eact.splits)+

lemma nil_btau_equiv_nil_iff[simp]:
  \<open>\<rho> \<simeq>\<^sub>\<tau>\<^sub>B [] \<longleftrightarrow> list_all (case_eact True basic_tau_aact) \<rho>\<close>
  by (induct \<rho>) (simp add: btau_equiv_trace_def split: eact.splits)+

lemma btau_equiv_trace_reflI[intro!]:
  \<open>\<rho> \<simeq>\<^sub>\<tau>\<^sub>B \<rho>\<close>
  by (metis btau_equiv_trace_def)

lemma btau_equiv_trace_reflp:
  \<open>reflp (\<simeq>\<^sub>\<tau>\<^sub>B)\<close>
  by (metis btau_equiv_trace_reflI reflpI)

lemma btau_equiv_trace_symp:
  \<open>symp (\<simeq>\<^sub>\<tau>\<^sub>B)\<close>
  by (metis btau_equiv_trace_def sympI)

lemma btau_equiv_trace_transp:
  \<open>transp (\<simeq>\<^sub>\<tau>\<^sub>B)\<close>
  by (metis btau_equiv_trace_def transpI)


lemma btau_equiv_Env_cons_equiv:
  \<open>Env # \<rho>x \<simeq>\<^sub>\<tau>\<^sub>B \<rho>x\<close>
  unfolding btau_equiv_trace_def
  by simp


lemma btau_equivR_appendL_rewrite:
  \<open>\<rho>y \<simeq>\<^sub>\<tau>\<^sub>B \<rho>y' \<Longrightarrow> \<rho>x \<simeq>\<^sub>\<tau>\<^sub>B \<rho>y @ \<rho>z \<longleftrightarrow> \<rho>x \<simeq>\<^sub>\<tau>\<^sub>B \<rho>y' @ \<rho>z\<close>
  unfolding btau_equiv_trace_def
  by force

lemma btau_equivR_appendR_rewrite:
  \<open>\<rho>z \<simeq>\<^sub>\<tau>\<^sub>B \<rho>z' \<Longrightarrow> \<rho>x \<simeq>\<^sub>\<tau>\<^sub>B \<rho>y @ \<rho>z \<longleftrightarrow> \<rho>x \<simeq>\<^sub>\<tau>\<^sub>B \<rho>y @ \<rho>z'\<close>
  unfolding btau_equiv_trace_def
  by force

lemma btau_equivL_appendL_rewrite:
  \<open>\<rho>x \<simeq>\<^sub>\<tau>\<^sub>B \<rho>x' \<Longrightarrow> \<rho>x @ \<rho>y \<simeq>\<^sub>\<tau>\<^sub>B \<rho>z \<longleftrightarrow> \<rho>x' @ \<rho>y \<simeq>\<^sub>\<tau>\<^sub>B \<rho>z\<close>
  unfolding btau_equiv_trace_def
  by force

lemma btau_equivL_appendR_rewrite:
  \<open>\<rho>y \<simeq>\<^sub>\<tau>\<^sub>B \<rho>y' \<Longrightarrow> \<rho>x @ \<rho>y \<simeq>\<^sub>\<tau>\<^sub>B \<rho>z \<longleftrightarrow> \<rho>x @ \<rho>y' \<simeq>\<^sub>\<tau>\<^sub>B \<rho>z\<close>
  unfolding btau_equiv_trace_def
  by force


subsubsection \<open> Basic-Tau Subtrace \<close>

definition less_eq_btau_trace :: \<open>aact eact list \<Rightarrow> aact eact list \<Rightarrow> bool\<close> (infix \<open>\<preceq>\<^sub>\<tau>\<^sub>B\<close> 55) where
  \<open>\<rho> \<preceq>\<^sub>\<tau>\<^sub>B \<rho>' \<equiv>
    List.filter (case_eact False (Not \<circ> basic_tau_aact)) \<rho> \<preceq>\<^sub>l
    List.filter (case_eact False (Not \<circ> basic_tau_aact)) \<rho>'\<close>

lemma nil_less_eq_btau_trace_iff[simp]:
  \<open>[] \<preceq>\<^sub>\<tau>\<^sub>B xs\<close>
  unfolding less_eq_btau_trace_def
  by force


subsection \<open> Atom Enabled \<close>

definition \<open>atom_enabled pq \<equiv> fst pq \<sqinter> pre_state (snd pq)\<close>


subsection \<open> Head Enabled Equivalent States \<close>

definition
  \<open>head_enabled_equiv c sx sy \<equiv> \<forall>a\<in>#head_atoms c. atom_enabled a sx = atom_enabled a sy\<close>

lemma head_enabled_equiv_skip_iff[simp]:
  \<open>head_enabled_equiv Skip sx sy\<close>
  \<open>head_enabled_equiv (ca ;; cb) sx sy \<longleftrightarrow> head_enabled_equiv ca sx sy\<close>
  \<open>head_enabled_equiv (ca \<^bold>\<sqinter> cb) sx sy\<close>
  \<open>head_enabled_equiv (ca \<^bold>\<box> cb) sx sy \<longleftrightarrow>
    head_enabled_equiv ca sx sy \<and> head_enabled_equiv cb sx sy\<close>
  \<open>head_enabled_equiv (ca \<parallel> cb) sx sy \<longleftrightarrow>
    head_enabled_equiv ca sx sy \<and> head_enabled_equiv cb sx sy\<close>
  \<open>head_enabled_equiv (DO c OD) sx sy \<longleftrightarrow>
    head_enabled_equiv c sx sy\<close>
  \<open>head_enabled_equiv \<langle>pa, qa\<rangle> sx sy \<longleftrightarrow>
    atom_enabled (pa, qa) sx = atom_enabled (pa, qa) sy\<close>
  unfolding head_enabled_equiv_def
  by (simp add: Ball_def Bex_def all_conj_distrib image_def imp_ex_conjL split: prod.splits)+

lemma head_enabled_equiv_reflI[intro!]:
  \<open>head_enabled_equiv c s s\<close>
  by (simp add: head_enabled_equiv_def)

lemma head_enabled_equiv_sym:
  \<open>head_enabled_equiv c sx sy \<Longrightarrow> head_enabled_equiv c sy sx\<close>
  by (force simp add: head_enabled_equiv_def)

lemma head_guard_trans_trans[trans]:
  \<open>head_enabled_equiv c sx sy \<Longrightarrow> head_enabled_equiv c sy sz \<Longrightarrow> head_enabled_equiv c sx sz\<close>
  by (force simp add: head_enabled_equiv_def)


subsection \<open> Do Loops \<close>

fun do_loops :: \<open>'s comm \<Rightarrow> 's comm multiset\<close> where
  \<open>do_loops Skip = {#}\<close>
| \<open>do_loops (ca;; cb) = do_loops ca \<union># do_loops cb\<close>
| \<open>do_loops (ca \<parallel> cb) = do_loops ca \<union># do_loops cb\<close>
| \<open>do_loops (ca \<^bold>\<sqinter> cb) = do_loops ca \<union># do_loops cb\<close>
| \<open>do_loops (ca \<^bold>\<box> cb) = do_loops ca \<union># do_loops cb\<close>
| \<open>do_loops \<langle>ar\<rangle> = {#}\<close>
| \<open>do_loops (DO c OD) = add_mset c (do_loops c)\<close>

paragraph \<open> Lemmas \<close>

text \<open> Doing this with multisets is false, as do-loops may duplicate parts of the command. \<close>
lemma aopstep_do_loops_subseteq:
  \<open>(s, c) \<midarrow>\<alpha>\<rightarrow>\<^sub>a (ms', c') \<Longrightarrow>
    set_mset (do_loops c') \<subseteq> set_mset (do_loops c)\<close>
  by (induct c arbitrary: s ms' c' \<alpha>)
    (fastforce simp add: if_bool_eq_disj conj_disj_distribL)+


subsection \<open> Do-Loop Enabled State Equivalence \<close>

abbreviation
  \<open>do_loop_head_enabled_equiv c sx sy \<equiv>
    \<forall>c'\<in>#do_loops c. head_enabled_equiv c' sx sy\<close>

lemma do_loop_head_enabled_equiv_iff[simp]:
  \<open>do_loop_head_enabled_equiv Skip sx sy\<close>
  \<open>do_loop_head_enabled_equiv \<langle>pa, qa\<rangle> sx sy\<close>
  \<open>do_loop_head_enabled_equiv (ca ;; cb) sx sy \<longleftrightarrow>
    do_loop_head_enabled_equiv ca sx sy \<and> do_loop_head_enabled_equiv cb sx sy\<close>
  \<open>do_loop_head_enabled_equiv (ca \<^bold>\<sqinter> cb) sx sy \<longleftrightarrow>
    do_loop_head_enabled_equiv ca sx sy \<and> do_loop_head_enabled_equiv cb sx sy\<close>
  \<open>do_loop_head_enabled_equiv (ca \<^bold>\<box> cb) sx sy \<longleftrightarrow>
    do_loop_head_enabled_equiv ca sx sy \<and> do_loop_head_enabled_equiv cb sx sy\<close>
  \<open>do_loop_head_enabled_equiv (ca \<parallel> cb) sx sy \<longleftrightarrow>
    do_loop_head_enabled_equiv ca sx sy \<and> do_loop_head_enabled_equiv cb sx sy\<close>
  \<open>do_loop_head_enabled_equiv (DO c OD) sx sy \<longleftrightarrow>
    head_enabled_equiv c sx sy \<and> do_loop_head_enabled_equiv c sx sy\<close>
  by (simp add: Ball_def all_conj_distrib)+

paragraph \<open> Lemmas \<close>

lemma no_aopstep_head_enabled_equiv_state_irrel:
  \<open>(sx, c) \<midarrow>/\<rightarrow>\<^sub>a \<Longrightarrow>
    head_enabled_equiv c sx sy \<Longrightarrow>
    (sy, c) \<midarrow>/\<rightarrow>\<^sub>a\<close>
proof (induct c arbitrary: sx sy)
  case (Endet c1 c2)
  then show ?case
    by (clarsimp split: if_splits, metis not_vis_aact_iff)
next
  case (Atomic x1 x2)
  then show ?case
    by (force simp add: if_bool_eq_disj atom_enabled_def pre_state_def)
qed (clarsimp simp add: all_conj_distrib; fail)+ (* slow *)


subsection \<open> Head Enabled Unique \<close>

definition
  \<open>head_enabled_unique c s \<equiv>
    \<forall>a\<in>#head_atoms c. \<forall>b\<in>#head_atoms c. atom_enabled a s = atom_enabled b s \<longrightarrow> a = b\<close>

subsubsection \<open> Do-guards Determinism \<close>

definition
  \<open>do_loops_determ c s \<equiv>
    (\<forall>c'\<in>#do_loops c.
      (\<forall>a. count (head_atoms c') a \<le> Suc 0) \<and>
      head_enabled_unique c' s)\<close>

lemma do_loops_determ_iff[simp]:
  \<open>do_loops_determ Skip s\<close>
  \<open>do_loops_determ \<langle>pa, qa\<rangle> s\<close>
  \<open>do_loops_determ (ca ;; cb) s \<longleftrightarrow>
    do_loops_determ ca s \<and> do_loops_determ cb s\<close>
  \<open>do_loops_determ (ca \<^bold>\<sqinter> cb) s \<longleftrightarrow>
    do_loops_determ ca s \<and> do_loops_determ cb s\<close>
  \<open>do_loops_determ (ca \<^bold>\<box> cb) s \<longleftrightarrow>
    do_loops_determ ca s \<and> do_loops_determ cb s\<close>
  \<open>do_loops_determ (ca \<parallel> cb) s \<longleftrightarrow>
    do_loops_determ ca s \<and> do_loops_determ cb s\<close>
  \<open>do_loops_determ (DO c OD) s \<longleftrightarrow>
    (\<forall>a. count (head_atoms c) a \<le> Suc 0) \<and>
    head_enabled_unique c s \<and>
    do_loops_determ c s\<close>
  unfolding do_loops_determ_def
  by (clarsimp simp add: ball_Un; fail)+

paragraph \<open> Lemmas \<close>

lemma aopstep_tau_determ_doloop_then_state_irrel:
  \<open>(s, c) \<midarrow>\<alpha>\<rightarrow>\<^sub>a (s', c') \<Longrightarrow>
    do_loop_head_enabled_equiv c s sa \<Longrightarrow>
    tau_aact \<alpha> \<Longrightarrow>
    (sa, c) \<midarrow>\<alpha>\<rightarrow>\<^sub>a (sa, c')\<close>
  apply (induct c arbitrary: \<alpha> s' c')
        apply fastforce
       apply fastforce
      apply fastforce
     apply fastforce
    apply (fastforce split: if_splits simp add: ball_Un)
   apply (fastforce split: if_splits simp add: ball_Un)
  apply clarsimp
  apply (metis no_aopstep_head_enabled_equiv_state_irrel)
  done

lemma aopsteps_tau_determ_doloop_then_state_irrel:
  \<open>(s, c) \<midarrow>\<rho>\<rightarrow>\<^sub>a\<^sup>* (s', c'') \<Longrightarrow>
    list_all tau_aact \<rho> \<Longrightarrow>
    do_loop_head_enabled_equiv c s sa \<Longrightarrow>
    (sa, c) \<midarrow>\<rho>\<rightarrow>\<^sub>a\<^sup>* (sa, c'')\<close>
  apply (induct \<rho> arbitrary: s c s' c'')
   apply force
  apply clarsimp
  apply (frule_tac sa=sa in aopstep_tau_determ_doloop_then_state_irrel, force, force)
  apply (rule exI[of _ \<open>fst sa\<close>], rule exI[of _ \<open>snd sa\<close>], rule_tac x=c' in exI)
  apply (frule aopstep_tau_preserves_state, blast)
  apply clarsimp
  apply (meson aopstep_do_loops_subseteq subsetD; fail)
  done

lemma btau_reduce_state_irrelevance:
  \<open>s, c \<leadsto>\<^sub>\<tau>\<^sub>B\<^sup>* c' \<Longrightarrow>
    do_loop_head_enabled_equiv c s sa \<Longrightarrow>
    sa, c \<leadsto>\<^sub>\<tau>\<^sub>B\<^sup>* c'\<close>
  unfolding btau_reduce_comm_def
  by (metis aopsteps_tau_determ_doloop_then_state_irrel basic_tau_aact_then_tau_aact
      list.pred_mono_strong)

text \<open> The main workhorse of the Conformant \<rightarrow> Exact transformation. \<close>
lemma astep_two_btau_sequencing:
  \<open>(s, c) \<midarrow>\<alpha>a\<rightarrow>\<^sub>a (s, cx') \<Longrightarrow>
    (s, c) \<midarrow>\<alpha>b\<rightarrow>\<^sub>a (s, cy') \<Longrightarrow>
    basic_tau_aact \<alpha>a \<Longrightarrow>
    basic_tau_aact \<alpha>b \<Longrightarrow>
    cx' \<noteq> cy' \<Longrightarrow>
    (\<exists>c'. (s, cy') \<midarrow>\<alpha>a\<rightarrow>\<^sub>a (s, c')) \<or>
    (\<exists>c'. (s, cx') \<midarrow>\<alpha>b\<rightarrow>\<^sub>a (s, c'))\<close>
  apply (induct c arbitrary: s \<alpha>a \<alpha>b cx' cy')
    (* Skip *)
        apply force
    (* Seq *)
       apply clarsimp
       apply (elim disjE)
          apply force
         apply force
        apply force
       apply clarsimp
       apply metis
    (* Parallel *)
      apply clarsimp
      apply (case_tac \<open>
  (\<exists>\<alpha>aa. \<alpha>a = PL \<alpha>aa) \<and> (\<exists>\<alpha>ab. \<alpha>b = PL \<alpha>ab) \<or>
  (\<exists>\<alpha>aa. \<alpha>a = PR \<alpha>aa) \<and> (\<exists>\<alpha>ab. \<alpha>b = PR \<alpha>ab)\<close>)
    (** the difficult cases **)
       apply (elim disjE[of \<open>_ \<and> Ex _\<close>])
        apply (clarsimp, blast)
       apply (clarsimp, blast)
    (** the rest **)
      apply (elim disjE; force)
    (* Indet *)
     apply force
    (* Endet *)
    apply clarsimp
    apply (case_tac \<open>
  (\<exists>ca. cx' = ca \<^bold>\<box> c2) \<and> (\<exists>ca. cy' = ca \<^bold>\<box> c2) \<or>
  (\<exists>cb. cx' = c1 \<^bold>\<box> cb) \<and> (\<exists>cb. cy' = c1 \<^bold>\<box> cb) \<or>
  (\<exists>cb. cx' = c1 \<^bold>\<box> cb) \<and> (\<exists>ca. cy' = ca \<^bold>\<box> c2) \<or>
  (\<exists>ca. cx' = ca \<^bold>\<box> c2) \<and> (\<exists>cb. cy' = c1 \<^bold>\<box> cb)\<close>)
      (** the difficult cases **)
     apply (elim disjE[of \<open>_ \<and> Ex _\<close>])
        apply (clarsimp, metis)
       apply (clarsimp, metis)
      apply force
     apply force
    (** the easy cases **)
    apply (elim disjE; simp; blast)
    (* Atom *)
   apply force
    (* Do-loop *)
  apply clarsimp
  apply (elim disjE)
     apply blast
    apply blast
   apply blast
  apply (clarsimp, metis)
  done

lemma btau_reduce_left_to_dstep_exact:
  \<open>sc \<midarrow>\<rho>x\<rightarrow>\<^sub>a\<^sub>r\<^sup>* mscx' \<Longrightarrow>
    sc = (s, c) \<Longrightarrow>
    mscx' = (s, cx) \<Longrightarrow>
    list_all basic_tau_aact \<rho>x \<Longrightarrow>
      (\<exists>cy. s, c \<leadsto>\<^sub>\<tau>\<^sub>B\<^sup>* cy \<and>
        (\<exists>\<rho>y. list_all (case_eact False basic_tau_aact) \<rho>y \<and>
          (((s, False), c), ((s, False), c))
            =R, F, (map Loc \<rho>x, \<rho>y)\<Rightarrow>\<^sub>\<E>\<^sup>*
            (((s, False), cx), ((s, False), cy))))\<close>
  apply (induct arbitrary: s c cx rule: aopsteps_rev.induct)
   apply force
  apply clarsimp
  apply (subst dexec_exact_left_rcons_iff)
  apply clarsimp
  sorry


definition
  \<open>invt_exec_prop p sc \<equiv> \<forall>\<rho> sc'. sc \<midarrow>\<rho>\<rightarrow>\<^sub>a\<^sup>* sc' \<longrightarrow> p sc'\<close>

lemma invt_exec_prop_iff:
  \<open>invt_exec_prop p (s, Skip) \<longleftrightarrow> p (s, Skip)\<close>
  \<open>invt_exec_prop p (s, ca ;; cb) \<longleftrightarrow>
    p (s, ca ;; cb) \<and>
    (\<forall>\<alpha> c1'. (s, ca) \<midarrow>\<alpha>\<rightarrow>\<^sub>a (Inr (), c1') \<longrightarrow> p (Inr (), c1' ;; cb)) \<and>
    (ca = Skip \<longrightarrow> invt_exec_prop p (s, cb)) \<and>
    (\<forall>s' ca'. (\<exists>\<alpha>. (s, ca) \<midarrow>\<alpha>\<rightarrow>\<^sub>a (s', ca')) \<longrightarrow> invt_exec_prop p (s', ca' ;; cb))\<close>
  \<open>invt_exec_prop p (s, ca \<^bold>\<sqinter> cb) \<longleftrightarrow>
    p (s, ca \<^bold>\<sqinter> cb) \<and>
    invt_exec_prop p (s, ca) \<and>
    invt_exec_prop p (s, cb)\<close>
  \<open>invt_exec_prop p (s, ca \<^bold>\<box> cb) \<longleftrightarrow>
    p (s, ca \<^bold>\<box> cb) \<and>
    (ca = Skip \<longrightarrow> invt_exec_prop p (s, cb)) \<and>
    (cb = Skip \<longrightarrow> invt_exec_prop p (s, ca)) \<and>
    (\<forall>\<alpha>. tau_aact \<alpha> \<longrightarrow>
      (\<forall>ca' s'. (s, ca) \<midarrow>\<alpha>\<rightarrow>\<^sub>a (s', ca') \<longrightarrow> invt_exec_prop p (s', ca' \<^bold>\<box> cb)) \<and>
      (\<forall>cb' s'. (s, cb) \<midarrow>\<alpha>\<rightarrow>\<^sub>a (s', cb') \<longrightarrow> invt_exec_prop p (s', ca \<^bold>\<box> cb'))) \<and>
    (\<forall>\<alpha>. vis_aact \<alpha> \<longrightarrow>
      (\<forall>ca'. (s, ca) \<midarrow>\<alpha>\<rightarrow>\<^sub>a (Inr (), ca') \<longrightarrow> p (Inr (), ca')) \<and>
      (\<forall>cb'. (s, cb) \<midarrow>\<alpha>\<rightarrow>\<^sub>a (Inr (), cb') \<longrightarrow> p (Inr (), cb')) \<and>
      (\<forall>s' ca'. (s, ca) \<midarrow>\<alpha>\<rightarrow>\<^sub>a (s', ca') \<longrightarrow> invt_exec_prop p (s', ca')) \<and>
      (\<forall>s' cb'. (s, cb) \<midarrow>\<alpha>\<rightarrow>\<^sub>a (s', cb') \<longrightarrow> invt_exec_prop p (s', cb')))\<close>
  \<open>invt_exec_prop p (s, ca \<parallel> cb) \<longleftrightarrow>
    p (s, ca \<parallel> cb) \<and>
    (ca = Skip \<longrightarrow> cb = Skip \<longrightarrow> p (s, Skip)) \<and>
    (\<forall>\<alpha> ca'. (s, ca) \<midarrow>\<alpha>\<rightarrow>\<^sub>a (Inr (), ca') \<longrightarrow> p (Inr (), ca' \<parallel> cb)) \<and>
    (\<forall>\<alpha> cb'. (s, cb) \<midarrow>\<alpha>\<rightarrow>\<^sub>a (Inr (), cb') \<longrightarrow> p (Inr (), ca \<parallel> cb')) \<and>
    (\<forall>\<alpha> s' ca'. (s, ca) \<midarrow>\<alpha>\<rightarrow>\<^sub>a (s', ca') \<longrightarrow> invt_exec_prop p (s', ca' \<parallel> cb)) \<and>
    (\<forall>\<alpha> s' cb'. (s, cb) \<midarrow>\<alpha>\<rightarrow>\<^sub>a (s', cb') \<longrightarrow> invt_exec_prop p (s', ca \<parallel> cb'))\<close>
  \<open>invt_exec_prop p (s, \<langle>pa, qa\<rangle>) \<longleftrightarrow>
    (p (s, \<langle>pa, qa\<rangle>) \<and>
    (\<not> pa s \<longrightarrow> p (Inr (), \<langle>pa, qa\<rangle>)) \<and>
    (pa s \<longrightarrow> (\<forall>a b. qa s (a, b) \<longrightarrow> p ((a, b), Skip))))\<close>
  \<open>invt_exec_prop p (s, DO c OD) \<longleftrightarrow>
    (p (s, DO c OD) \<and>
    ((\<exists>\<alpha> c'. (s, c) \<midarrow>\<alpha>\<rightarrow>\<^sub>a (Inr (), c')) \<longrightarrow> p (Inr (), DO c OD)) \<and>
    ((\<forall>\<alpha> a b c'. \<not> (s, c) \<midarrow>\<alpha>\<rightarrow>\<^sub>a ((a, b), c')) \<longrightarrow> p (s, Skip)) \<and>
    (\<forall>\<alpha> s' c'. (s, c) \<midarrow>\<alpha>\<rightarrow>\<^sub>a (s', c') \<longrightarrow> invt_exec_prop p (s', c' ;; DO c OD)))\<close>
  (* Skip *)
        apply (simp add: invt_exec_prop_def)
    (* Seq *)
       apply (simp add: invt_exec_prop_def)
       apply (subst aopsteps_iff)
       apply (clarsimp simp add: all_conj_distrib imp_ex_conjL imp_conjL ex_disj_distrib
      conj_disj_distribR split_pairs split_pairs2)
       apply blast
    (* Indet *)
      apply (simp add: invt_exec_prop_def)
      apply (subst aopsteps_iff)
      apply (clarsimp simp add: all_conj_distrib imp_ex_conjL imp_conjL ex_disj_distrib
      conj_disj_distribR split_pairs split_pairs2)
      apply blast
    (* Endet *)
     apply (simp add: invt_exec_prop_def)
     apply (subst aopsteps_iff)
     apply (clarsimp simp add: all_conj_distrib imp_ex_conjL imp_conjL imp_conjR ex_disj_distrib
      conj_disj_distribR split_pairs split_pairs2)
     apply (rule iffI, force)
     apply clarsimp
     apply (metis aopstep_tau_preserves_state fst_conv sum.distinct(1))
    (* Parallel *)
    apply (simp add: invt_exec_prop_def)
    apply (subst aopsteps_iff)
    apply (clarsimp simp add: all_conj_distrib imp_ex_conjL imp_conjL imp_conjR ex_disj_distrib
      conj_disj_distribR split_pairs split_pairs2)
    apply blast
    (* Atom *)
   apply (simp add: invt_exec_prop_def)
   apply (subst aopsteps_iff)
   apply (force simp add: all_conj_distrib imp_ex_conjL)
    (* Do-loop *)
  apply (simp add: invt_exec_prop_def)
  apply (subst aopsteps_iff)
  apply (clarsimp simp add: all_conj_distrib imp_ex_conjL imp_conjL imp_conjR ex_disj_distrib
      conj_disj_distribR split_pairs split_pairs2)
  apply blast
  done


definition
  \<open>comm_determ sc \<equiv> \<forall>\<rho> sc'. sc \<midarrow>\<rho>\<rightarrow>\<^sub>a\<^sup>* sc' \<longrightarrow> (\<forall>sc''. sc \<midarrow>\<rho>\<rightarrow>\<^sub>a\<^sup>* sc'' \<longrightarrow> snd sc' = snd sc'')\<close>

definition
  \<open>hatoms_determ \<equiv> (\<lambda>(ms,c).
      \<forall>s. ms = s \<longrightarrow> (\<forall>pq\<in>#head_atoms c. \<forall>pq'\<in>#head_atoms c.
        fst pq s \<sqinter> pre_state (snd pq) s = fst pq' s \<sqinter> pre_state (snd pq') s))\<close>

abbreviation \<open>invt_hatoms_determ \<equiv> invt_exec_prop hatoms_determ\<close>


lemma aopstep_hatoms_determ_implies_comm_determ':
  \<open>sc \<midarrow>\<alpha>\<rightarrow>\<^sub>a sc' \<Longrightarrow>
    sc \<midarrow>\<alpha>\<rightarrow>\<^sub>a sc'' \<Longrightarrow>
    hatoms_determ ((fst sc), snd sc) \<Longrightarrow>
    snd sc' = snd sc''\<close>
  apply (induct arbitrary: sc'' rule: aopstep_induct)
        apply force
       apply clarsimp
       apply (elim disjE)
          apply force
         apply force
        apply force
       apply clarsimp
       apply (subst (asm)(2) hatoms_determ_def)
       apply (simp split: prod.splits)
  sorry

lemma aopstep_preserves_hatoms_determ:
  \<open>sc \<midarrow>\<alpha>\<rightarrow>\<^sub>a sc' \<Longrightarrow>
    sc' = (s', c') \<Longrightarrow>
    hatoms_determ sc \<Longrightarrow>
    hatoms_determ (s', c')\<close>
  apply (induct arbitrary: s' c' rule: aopstep_induct)
        apply force
       apply clarsimp
  sorry

lemma aopsteps_hatoms_determ_implies_comm_determ':
  \<open>sc \<midarrow>\<rho>\<rightarrow>\<^sub>a\<^sup>* sc' \<Longrightarrow>
    sc \<midarrow>\<rho>\<rightarrow>\<^sub>a\<^sup>* sc'' \<Longrightarrow>
    hatoms_determ sc \<Longrightarrow>
    snd sc' = snd sc''\<close>
  apply (induct arbitrary: sc'' rule: aopsteps_induct)
    apply force
   apply clarsimp
   apply (metis aopstep_hatoms_determ_implies_comm_determ' snd_conv)
  apply clarsimp
  apply (erule disjE)
   apply clarsimp
   apply (frule aopstep_hatoms_determ_implies_comm_determ', blast, blast)
   apply clarsimp
  sorry

lemma
  \<open>hatoms_determ sc \<Longrightarrow> comm_determ sc\<close>
  apply (clarsimp simp add: hatoms_determ_def comm_determ_def)
  oops

lemma dstep_conf_to_dexec_exact:
  assumes
    \<open>(((sx, kx), cx), ((sy, ky), cy))
      =R, F, (\<rho>x, \<rho>y)\<Rightarrow>\<^sub>\<C> (((sx', kx'), cx'), ((sy', ky'), cy'))\<close>
    \<open>sx, cx \<leadsto>\<^sub>\<tau>\<^sub>B\<^sup>* cy \<or> sy, cy \<leadsto>\<^sub>\<tau>\<^sub>B\<^sup>* cx\<close>
    \<open>\<forall>p\<in>do_loops cx. p sx = p sx'\<close>
    \<open>\<forall>p\<in>do_loops cy. p sy = p sy'\<close>
  shows
    \<open>\<exists>c c'.
      (c = cx \<and> c' = cx' \<and> sx, cx \<leadsto>\<^sub>\<tau>\<^sub>B\<^sup>* cy \<and> sx', cx' \<leadsto>\<^sub>\<tau>\<^sub>B\<^sup>* cy'
        \<or> c = cy \<and> c' = cy' \<and> sy, cy \<leadsto>\<^sub>\<tau>\<^sub>B\<^sup>* cx \<and> sy', cy' \<leadsto>\<^sub>\<tau>\<^sub>B\<^sup>* cx') \<and>
    (\<exists>\<rho>x'. \<rho>x \<simeq>\<^sub>\<tau>\<^sub>B \<rho>x' \<and>
    (\<exists>\<rho>y'. \<rho>y \<simeq>\<^sub>\<tau>\<^sub>B \<rho>y' \<and>
      (((sx, kx), c), ((sy, ky), c))
        =R, F, (\<rho>x', \<rho>y')\<Rightarrow>\<^sub>\<E>\<^sup>* (((sx', kx'), c'), ((sy', ky'), c'))))\<close>
  using assms(1)
proof (elim dstep_conf.cases)
  presume assms2:
    \<open>\<rho>x = [Env]\<close>
    \<open>\<rho>y = [Env]\<close>
    \<open>R (snd sx, snd sy) (snd sx', snd sy')\<close>
    \<open>fst sx' = fst sx\<close>
    \<open>fst sy' = fst sy\<close>
    \<open>kx' = kx\<close>
    \<open>cx' = cx\<close>
    \<open>ky' = ky\<close>
    \<open>cy' = cy\<close>
  then show ?thesis
    using assms(2-)
    apply clarsimp
    apply (erule disjE)
     apply (rule exI[where x=cx], rule exI[where x=cx'])
     apply (rule conjI, metis btau_reduce_state_irrelevance)
     apply (rule exI[where x=\<open>[Env]\<close>], rule conjI, blast)
     apply (rule exI[where x=\<open>[Env]\<close>], rule conjI, blast)
      (* In the following, "; force" would be nicer, but it doesn't work due to unification order.*)
     apply (rule dexec_exact_step_env[OF dexec_nil, simplified], (force+)[10])
    apply (rule exI[where x=cy], rule exI[where x=cy'])
    apply (rule conjI, metis btau_reduce_state_irrelevance)
    apply (rule exI[where x=\<open>[Env]\<close>], rule conjI, blast)
    apply (rule exI[where x=\<open>[Env]\<close>], rule conjI, blast)
    apply (rule dexec_exact_step_env[OF dexec_nil, simplified], (force+)[10])
    done
next
  fix fx \<alpha>
  presume
    \<open>\<rho>x = [Loc \<alpha>]\<close>
    \<open>\<rho>y = []\<close>
    \<open>sx' = sx\<close>
    \<open>\<not> kx\<close>
    \<open>sy' = sy\<close>
    \<open>kx'\<close>
    \<open>cy' = cy\<close>
    \<open>\<exists>fy. F ((fx, fy), snd sx', snd sy') \<and> fst sy' ## fy\<close>
    \<open>fst sx' ## fx\<close>
    \<open>((fst sx' + fx, snd sx'), cx) \<midarrow>\<alpha>\<rightarrow>\<^sub>a (Inr (), cx')\<close>
  then show ?thesis
    sorry
next
  fix fy \<alpha>
  presume
    \<open>\<rho>x = []\<close>
    \<open>\<rho>y = [Loc \<alpha>]\<close>
    \<open>\<not> ky\<close>
    \<open>sx' = sx\<close>
    \<open>kx' = kx\<close>
    \<open>cx' = cx\<close>
    \<open>sy' = sy\<close>
    \<open>ky'\<close>
    \<open>\<exists>fx. F ((fx, fy), snd sx', snd sy') \<and> fst sx' ## fx\<close>
    \<open>fst sy' ## fy\<close>
    \<open>((fst sy' + fy, snd sy'), cy) \<midarrow>\<alpha>\<rightarrow>\<^sub>a (Inr (), cy')\<close>
  then show ?thesis
    sorry
next
  fix fx sx \<alpha> cy cx
  presume
    \<open>\<rho>x = [Loc \<alpha>]\<close>
    \<open>\<rho>y = []\<close>
    \<open>ss = (((sx, False), cx), (sy', ky'), cy)\<close>
    \<open>\<not> kx'\<close>
    \<open>\<exists>fy. F ((fx, fy), snd sx, snd sy') \<and> fst sy' ## fy\<close>
    \<open>nonsync_aact \<alpha>\<close>
    \<open>fst sx ## fx\<close>
    \<open>((fst sx + fx, snd sx), cx) \<midarrow>\<alpha>\<rightarrow>\<^sub>a ((fst sx' + fx, snd sx'), cx')\<close>
  then show ?thesis
    sorry
next
  fix fy sy \<alpha> cy
  presume
    \<open>\<rho>x = []\<close>
    \<open>\<rho>y = [Loc \<alpha>]\<close>
    \<open>ss = (((sx', kx'), cx'), (sy, False), cy)\<close>
    \<open>\<not> ky'\<close>
    \<open>\<exists>fx. F ((fx, fy), snd sx', snd sy) \<and> fst sx' ## fx\<close>
    \<open>nonsync_aact \<alpha>\<close>
    \<open>fst sy ## fy\<close>
    \<open>((fst sy + fy, snd sy), cy) \<midarrow>\<alpha>\<rightarrow>\<^sub>a ((fst sy' + fy, snd sy'), cy')\<close>
  show ?thesis
    sorry
next
  fix fx fy sx sy \<alpha> cx cy 
  presume
    \<open>\<rho>x = [Loc \<alpha>]\<close>
    \<open>\<rho>y = [Loc \<alpha>]\<close>
    \<open>ss = (((sx, False), cx), (sy, False), cy)\<close>
    \<open>\<not> kx'\<close>
    \<open>\<not> ky'\<close>
    \<open>F ((fx, fy), snd sx, snd sy)\<close>
    \<open>\<not> nonsync_aact \<alpha>\<close>
    \<open>fst sx ## fx\<close>
    \<open>((fst sx + fx, snd sx), cx) \<midarrow>\<alpha>\<rightarrow>\<^sub>a ((fst sx' + fx, snd sx'), cx')\<close>
    \<open>fst sx ## fx\<close>
    \<open>((fst sy + fy, snd sy), cy) \<midarrow>\<alpha>\<rightarrow>\<^sub>a ((fst sy' + fy, snd sy'), cy')\<close>
  then show ?thesis
    sorry
qed force+


lemma ragged_dstep_conf_completion:
  \<open>ss' =R, F, (\<rho>xa', \<rho>ya')\<Rightarrow>\<^sub>\<C> ss'' \<Longrightarrow> \<comment> \<open> next step \<close>
    ss' =R, F, (\<rho>x', \<rho>y')\<Rightarrow>\<^sub>\<C>\<^sup>* ss''' \<Longrightarrow> \<comment> \<open> old completion \<close>
    \<rho>xa @ \<rho>x' \<simeq>\<^sub>\<tau>\<^sub>B \<rho>ya @ \<rho>y' \<Longrightarrow>
    list_all (case_eact True basic_tau_aact) \<rho>x' \<or> list_all (case_eact True basic_tau_aact) \<rho>y' \<Longrightarrow>
    list_all (case_eact False \<top>) \<rho>x' \<Longrightarrow>
    list_all (case_eact False \<top>) \<rho>y' \<Longrightarrow>
    snd (fst ss''') = snd (snd ss''') \<Longrightarrow>
    \<rho>x = \<rho>xa @ \<rho>xa' \<Longrightarrow>
    \<rho>y = \<rho>ya @ \<rho>ya' \<Longrightarrow>
    \<exists>\<rho>x' \<rho>y'.
      (\<exists>ssx'''. ss'' =R, F, (\<rho>x', \<rho>y')\<Rightarrow>\<^sub>\<C>\<^sup>* ssx''' \<and> snd (fst ssx''') = snd (snd ssx''')) \<and>
      \<rho>xa @ \<rho>xa' @ \<rho>x' \<simeq>\<^sub>\<tau>\<^sub>B \<rho>ya @ \<rho>ya' @ \<rho>y' \<and>
      (list_all (case_eact True basic_tau_aact) \<rho>x' \<or> list_all (case_eact True basic_tau_aact) \<rho>y') \<and>
      list_all (case_eact False \<top>) \<rho>x' \<and>
      list_all (case_eact False \<top>) \<rho>y'\<close>
  apply (erule dstep_conf.cases)
(* EnvEnv *)
       apply clarify
       apply (rename_tac lsx' ssx' lsy' ssy' lsx'' ssx'' lsy'' ssy'' u kx' cx' ky' cy')
       apply (clarsimp simp del: split_paired_Ex simp add:
      btau_equivR_appendR_rewrite[OF btau_equiv_Env_cons_equiv]
      btau_equivL_appendR_rewrite[OF btau_equiv_Env_cons_equiv])
       apply (rule_tac x=\<rho>x' in exI)
       apply (rule_tac x=\<rho>y' in exI)
       apply (clarsimp simp del: split_paired_Ex)
       apply (rule_tac x=ss''' in exI)
       apply (rule conjI)
    (* CrashL *)
    (* CrashR *)
    (* LocL *)
    (* LocR *)
    (* LocLoc *)
  sorry

lemma ragged_dexec_conf_completion:
  \<open>ss =R, F, \<rho>\<rho>\<Rightarrow>\<^sub>\<C>\<^sup>* ss' \<Longrightarrow>
    ss = (((sx, False), c), (sy, False), c) \<Longrightarrow>
    \<rho>\<rho> = (\<rho>x, \<rho>y) \<Longrightarrow>
    \<exists>\<rho>x' \<rho>y' ss''.
      ss' =R, F, (\<rho>x', \<rho>y')\<Rightarrow>\<^sub>\<C>\<^sup>* ss'' \<and>
      \<rho>x @ \<rho>x' \<simeq>\<^sub>\<tau>\<^sub>B \<rho>y @ \<rho>y' \<and>
      (\<rho>x' \<simeq>\<^sub>\<tau>\<^sub>B [] \<or> \<rho>y' \<simeq>\<^sub>\<tau>\<^sub>B []) \<and>
      list_all (case_eact False \<top>) \<rho>x' \<and>
      list_all (case_eact False \<top>) \<rho>y' \<and>
      snd (fst ss'') = snd (snd ss'')\<close>
proof (induct arbitrary: \<rho>x \<rho>y rule: dexec_conf_induct)
  case (Nil ss' ss)
  then show ?case
    by fastforce
next
  case (Append \<rho>xa \<rho>ya ss ss' \<rho>xa' \<rho>ya' ss'')

  obtain \<rho>x' \<rho>y' ssa'' where IH:
    \<open>ss' =R, F, (\<rho>x', \<rho>y')\<Rightarrow>\<^sub>\<C>\<^sup>* ssa''\<close>
    \<open>\<rho>xa @ \<rho>x' \<simeq>\<^sub>\<tau>\<^sub>B \<rho>ya @ \<rho>y'\<close>
    \<open>\<rho>x' \<simeq>\<^sub>\<tau>\<^sub>B [] \<or> \<rho>y' \<simeq>\<^sub>\<tau>\<^sub>B []\<close>
    \<open>list_all (case_eact False \<top>) \<rho>x'\<close>
    \<open>list_all (case_eact False \<top>) \<rho>y'\<close>
    \<open>snd (fst ssa'') = snd (snd ssa'')\<close>
    using Append.prems(1) Append.hyps(2)
    by blast
  
  show ?case
    using Append.prems Append.hyps(1,3) IH
    apply clarsimp
    apply (frule(8) ragged_dstep_conf_completion)
    apply (clarsimp simp add: top_fun_def)
    done
qed

lemma matching_dexec_conf_to_exact_exec:
  \<open>ss =R, F, \<rho>\<rho>\<Rightarrow>\<^sub>\<C>\<^sup>* ss' \<Longrightarrow>
    \<rho>x \<simeq>\<^sub>\<tau>\<^sub>B \<rho>y \<Longrightarrow>
    \<rho>\<rho> = (\<rho>x, \<rho>y) \<Longrightarrow>
    ss = (((sx, False), c), (sy, False), c) \<Longrightarrow>
    ss' = (((sx', kx'), c'), ((sy', ky'), c')) \<Longrightarrow>
    (\<exists>ms''.
      (\<not> kx' \<and> \<not> ky' \<and> ms'' = (exch4 (sx', sy')) \<or>
        ((kx' \<or> ky') \<and> ms'' = Inr ())) \<and>
      \<comment> \<open> we could equivalently choose \<open>\<rho>y\<close> \<close>
      (exch4 (sx, sy), c \<times>\<^sub>C c) \<midarrow>R, F, \<rho>x\<rightarrow>\<^sub>e\<^sub>a\<^sup>* (ms'', c' \<times>\<^sub>C c'))\<close>
  sorry


text \<open>
  This lemma uses lemma \<open>dstep_conf_to_dexec_exact\<close>, but note the proof is *not* by simple repeated
  application of this theorem and concatenation of the resulting exact traces.

  The \<C> evaluation may end on a 'ragged edge', with non-matching commands and vis steps.
  This is turned into a 'clean edge' with matching commands and basic-tau equivalent traces.
  To do this, the incomplete execution must be extended. (As Vis moves are deterministic,
  at most one execution may lag behind the other, such that it can be extended to match Vis
  moves again.)
    The issue to be dealt with here is that we need a relation between the commands of the ragged
  edge, and the final command of the synchronised execution, so the induction can be extended. This
  relationship is as follows: the synchronised-command must be a \<open>\<leadsto>\<^sub>\<tau>\<^sub>B\<^sup>*\<close> from both commands of
  the *Vis-completed* \<C>-execution.
\<close>
lemma dstep_conf_to_dexec_exact:
  \<open>ss =R, F, \<rho>\<rho>\<Rightarrow>\<^sub>\<C>\<^sup>* ss' \<Longrightarrow>
    ss = (((sx, False), c), (sy, False), c) \<Longrightarrow>
    ss' = (((sx', kx'), cx'), (sy', ky'), cy') \<Longrightarrow>
    \<rho>\<rho> = (\<rho>x, \<rho>y) \<Longrightarrow>
    \<exists>\<rho>x' \<rho>y' ss''.
      ss' =R, F, (\<rho>x', \<rho>y')\<Rightarrow>\<^sub>\<C>\<^sup>* ss'' \<and>
      \<rho>x @ \<rho>x' \<simeq>\<^sub>\<tau>\<^sub>B \<rho>y @ \<rho>y' \<and>
      (\<rho>x' \<simeq>\<^sub>\<tau>\<^sub>B [] \<or> \<rho>y' \<simeq>\<^sub>\<tau>\<^sub>B []) \<and>
      (\<exists>c'' sx'' kx'' sy'' ky''.
        ss'' = (((sx'', kx''), c''), ((sy'', ky''), c'')) \<and>
        (\<exists>ms''.
          (\<not> kx'' \<and> \<not> ky'' \<and> ms'' = (exch4 (sx'', sy'')) \<or>
            ((kx'' \<or> ky'') \<and> ms'' = Inr ())) \<and>
          \<comment> \<open> we could equivalently choose \<open>\<rho>y @ \<rho>y'\<close> \<close>
          (exch4 (sx, sy), c \<times>\<^sub>C c) \<midarrow>R, F, \<rho>x @ \<rho>x'\<rightarrow>\<^sub>e\<^sub>a\<^sup>* (ms'', c'' \<times>\<^sub>C c'')))\<close>
  apply (frule ragged_dexec_conf_completion, blast, blast)
  apply clarsimp
  apply (frule(1) dexec_trans)
  apply clarsimp
  apply (frule(1) matching_dexec_conf_to_exact_exec, blast, blast, blast)
  apply clarsimp
  apply blast
  done


proof (induct arbitrary: sx c sy sx' kx' cx' sy' ky' cy' \<rho>x \<rho>y rule: dexec_conf_induct)
  case (Nil ss' ss)
  then show ?case
    by fastforce
next
  case (Append \<rho>xa \<rho>ya ss ss' \<rho>xb \<rho>yb ss'')

  obtain \<rho>xa' \<rho>ya' msa'' sxa'' kxa'' sya'' kya'' ca'' where IH:
    \<open>ss' =R, F, (\<rho>xa', \<rho>ya')\<Rightarrow>\<^sub>\<C>\<^sup>* (((sxa'', kxa''), ca''), ((sya'', kya''), ca''))\<close>
    \<open>\<rho>xa @ \<rho>xa' \<simeq>\<^sub>\<tau>\<^sub>B \<rho>ya @ \<rho>ya'\<close>
    \<open>(list_all (case_eact True basic_tau_aact) \<rho>xa' \<or> list_all (case_eact True basic_tau_aact) \<rho>ya')\<close>
    \<open>\<not> kxa'' \<and> \<not> kya'' \<and> msa'' = (exch4 (sxa'', sya'')) \<or>
      (kxa'' \<or> kya'') \<and> msa'' = Inr ()\<close>
    \<open>(exch4 (fst (fst (fst ss)), fst (fst (snd ss))), snd (fst ss) \<times>\<^sub>C snd (fst ss))
      \<midarrow>R, F, \<rho>xa @ \<rho>xa'\<rightarrow>\<^sub>e\<^sub>a\<^sup>*
      (msa'', ca'' \<times>\<^sub>C ca'')\<close>
    using Append.prems(1) Append.hyps(2)
    apply (clarsimp simp add: split_pairs2 top_fun_def)
    apply (drule meta_spec2, drule meta_spec, (drule meta_mp, blast)+)
    apply force
    done

  show ?case
    using Append.prems Append.hyps(1,3) IH
    apply (clarsimp simp add: split_pairs2)
    sorry
qed
find_theorems \<open>_ = (_,_) \<longleftrightarrow> _ \<and> _\<close>

lemma dexec_conf_to_eaopsteps:
  \<open>ss =R, F, \<rho>\<rho>\<Rightarrow>\<^sub>\<C>\<^sup>* ss' \<Longrightarrow>
    ss = (((sx, kx), c), ((sy, ky), c)) \<Longrightarrow>
    ss' = (((sx', kx'), cx'), ((sy', ky'), cy')) \<Longrightarrow>
    \<rho>\<rho> = (\<rho>x, \<rho>y) \<Longrightarrow>
    \<exists>ms' c' \<rho>.
      sx', cx' \<leadsto>\<^sub>\<tau>\<^sub>B\<^sup>* c' \<and>
      sy', cy' \<leadsto>\<^sub>\<tau>\<^sub>B\<^sup>* c' \<and>
      (\<rho>x \<simeq>\<^sub>\<tau>\<^sub>B \<rho> \<and> \<rho>y \<preceq>\<^sub>\<tau>\<^sub>B \<rho> \<or> \<rho>x \<preceq>\<^sub>\<tau>\<^sub>B \<rho> \<and> \<rho>y \<simeq>\<^sub>\<tau>\<^sub>B \<rho>) \<and>
      ((\<not> kx' \<and> \<not> ky' \<or> \<rho>x = [] \<and> \<rho>y = []) \<and> ms' = (exch4 (sx', sy')) \<or>
        (kx' \<or> ky') \<and> (\<rho>x \<noteq> [] \<or> \<rho>y \<noteq> []) \<and> ms' = Inr ()) \<and>
      (exch4 (sx, sy), c \<times>\<^sub>C c) \<midarrow>R, F, \<rho>\<rightarrow>\<^sub>e\<^sub>a\<^sup>* (ms', c' \<times>\<^sub>C c')\<close>
proof (induct arbitrary: sx kx sy ky c sx' kx' cx' sy' ky' cy' \<rho>x \<rho>y rule: dexec_conf_induct)
  case (Nil zz' zz)
  then show ?case
    by (fastforce intro!: exI[of _ \<open>[]\<close>])
next
  case (Append \<rho>x \<rho>y ss ss' \<rho>x' \<rho>y' ss'' _ _ _ _ _ sx'' kx'' cx'' sy'' ky'' cy'' \<rho>x'' \<rho>y'')
  then show ?case
    apply (clarsimp simp add: less_eq_btau_trace_def)
    sorry
qed



lemma dexec_exact_and_safe_to_secure:
  \<open>ss =R, F, \<rho>\<rho>\<Rightarrow>\<^sub>\<E>\<^sup>* ss' \<Longrightarrow>
    safe (max (length (fst \<rho>\<rho>)) (length (snd \<rho>\<rho>)))
      (liftC' (snd (fst ss)) (snd (snd ss)))
      ((exch4 (fst (fst (fst ss)), fst (fst (snd ss)))))
      R G q S F \<Longrightarrow>
    L (exch4 (fst (fst ss), fst (snd ss))) \<Longrightarrow>
    L (exch4 (fst (fst ss'), fst (snd ss')))\<close>
  apply (induct rule: dexec_exact_induct)
   apply force
  apply clarsimp
  apply (erule dstep_exact.cases)
    apply (clarsimp simp add: safe_suc_iff)
  oops

lemma dexec_exact_and_safe_to_secure:
  \<open>ss =R, F, \<rho>\<rho>\<Rightarrow>\<^sub>\<E>\<^sup>* ss' \<Longrightarrow>
    ss = (((s, kx), cx), ((s, ky), cy)) \<Longrightarrow>
    ss' = (((sx', kx'), cx'), ((sy', ky'), cy')) \<Longrightarrow>
    \<rho>\<rho> = (\<rho>x, \<rho>y) \<Longrightarrow>
    safe n (liftC' c c) ((exch4 (s, s))) R G q S F \<Longrightarrow>
    s, c \<leadsto>\<^sub>\<tau>\<^sub>B\<^sup>* cx \<Longrightarrow>
    s, c \<leadsto>\<^sub>\<tau>\<^sub>B\<^sup>* cy \<Longrightarrow>
    length \<rho>x < n \<Longrightarrow>
    length \<rho>y < n \<Longrightarrow>
    \<exists>cx'' cy'' \<rho>x' \<rho>y'.
      sx', cx' \<leadsto>\<^sub>\<tau>\<^sub>B\<^sup>* cx'' \<and>
      sy', cy' \<leadsto>\<^sub>\<tau>\<^sub>B\<^sup>* cy'' \<and>
      \<rho>x \<simeq>\<^sub>\<tau>\<^sub>B \<rho>x' \<and>
      \<rho>y \<simeq>\<^sub>\<tau>\<^sub>B \<rho>y' \<and>
      ss =R, F, (\<rho>x', \<rho>y')\<Rightarrow>\<^sub>\<S>\<^sup>* (((sx', kx'), cx''), ((sy', ky'), cy''))\<close>

theorem security:
  fixes n :: nat
    and cx cy :: \<open>('l::pre_perm_alg \<times> 's) comm\<close>
    and sx sy :: \<open>'l \<times> 's\<close>
  assumes noninductive_assms:
    \<open>FF \<le> (cancellative \<times>\<^sub>P cancellative) \<times>\<^sub>P \<top>\<close>
    \<open>\<forall>sx sy sx' sy'. RR (sx, sy) (sx', sy') \<longrightarrow>
      (\<forall>lxy. FF (lxy, (sx, sy)) \<longrightarrow> FF (lxy, (sx', sy')))\<close>
    and inductive_assms:
    \<open>zxy =RR, FF, C, \<delta>xy\<Rightarrow>\<^sub>\<C>\<^sup>* zxy'\<close>
    \<open>zxy = ((sx, cx), (sy, cy))\<close>
    \<open>safe n (liftC' cx cy) ((exch4 (sx, sy))) RR GG qq SS FF\<close>
    \<open>btau_equiv (sx, cx) (sy, cy)\<close>
    \<open>length (fst \<delta>xy) < n\<close>
    \<open>length (snd \<delta>xy) < n\<close>
    \<open>S \<circ> exch4 \<le> sec_head_determ cx\<close>
    \<open>S \<circ> exch4 \<le> sec_head_determ cy\<close>
    \<open>C cx cy\<close>
    \<open>(=) \<le> C\<close>
  shows
    \<open>zxy =RR, FF, C, \<delta>xy\<Rightarrow>\<^sub>\<S>\<^sup>* zxy'\<close>
  using inductive_assms
proof (induction arbitrary: sx cx sy cy n rule: dsteps_conf.induct)
  case (dsteps_conf_nil zz' zz RR FF CC)
  then show ?case
    apply clarsimp
    apply (rule dexec_nil; force)
    done
next
  case (dsteps_conf_step zz sxx cxx syy cyy RR FF
      \<delta>xx \<delta>yy zz' CC \<delta>x' \<delta>y' zz'')

  note ih = dsteps_conf_step(5)[
      where sx=\<open>(sxl, sxs)\<close> and sy=\<open>(syl, sys)\<close> for sxl sxs syl sys,
        simplified]

  obtain sxl sxs where \<open>sxx = (sxl, sxs)\<close>
    by (metis (full_types) prod.exhaust)
  moreover obtain syl sys where \<open>syy = (syl, sys)\<close>
    by (metis (full_types) prod.exhaust)
  moreover obtain sxl' sxs'
    where \<open>fst (fst zz') = (sxl', sxs') \<or> fst (fst zz') = Inr ()\<close>
    by (metis (mono_tags) sum.exhaust unit.exhaust prod.exhaust)
  moreover obtain syl' sys'
    where \<open>fst (snd zz') = (syl', sys') \<or> fst (snd zz') = Inr ()\<close>
    by (metis (mono_tags) sum.exhaust unit.exhaust prod.exhaust)
  ultimately show ?case
    using dsteps_conf_step.prems dsteps_conf_step.hyps
    apply clarsimp
    apply (erule dstep_conf.cases)
      (* Env/Env *)
         apply (clarsimp simp add: Suc_less_eq2)
         apply (rule_tac zz'=\<open>(((sxl, sxs'), ux), ((syl, sys'), uy))\<close>
        for ux uy in dexec_doublestepI, (simp; fail))
           apply (rule dstep_secure_env[where sx'=\<open>(_,_)\<close> and sy'=\<open>(_,_)\<close>],
        (simp; fail), (simp; fail), (simp; fail), (simp; fail), (simp; fail))
          apply (simp; fail)
         apply (clarsimp simp add: safe_suc_iff)
         apply (drule spec2, drule mp, assumption)
         apply (frule ih[rotated 2]; blast)
      (* Loc/\<epsilon> Crash *)
        apply clarsimp
    apply (frule dsteps_conf_left_crash_preserved_fwd, (simp; fail))
    subgoal sorry
      (* \<epsilon>/Loc Crash *)
       apply clarsimp
       apply (frule dsteps_conf_right_crash_preserved_fwd, (simp; fail))
    subgoal sorry
      (* Loc/\<epsilon> *)
      apply clarsimp
      apply (case_tac \<open>basic_tau_aact \<alpha>\<close>)
      (* basic tau *)
       apply (rule dexec_step_leftI[OF
          _ dstep_secure_btau_left[where sx'=\<open>(_,_)\<close>]])
             apply (simp; fail)
            apply (clarsimp, blast)
           apply (simp; fail)
          apply (simp; fail)
         apply (clarsimp, blast)
        apply (simp; fail)
    subgoal sorry
        (* not basic tau *)
    subgoal sorry
        (*
      apply (clarsimp simp add: Suc_less_eq2)
      apply (frule_tac cx=cx' and n=\<open>m'\<close> in ih[rotated 2]) *)
    sorry
qed




section \<open> Examples \<close>

(* TODO: move *)

lemma eq_rtimes_R_iff:
  \<open>((=) \<times>\<^sub>R r) s s' \<longleftrightarrow> r (snd s) (snd s') \<and> fst s = fst s'\<close>
  by (cases s, cases s', force)

lemma top_rtimes_R_iff:
  \<open>(\<top> \<times>\<^sub>R r) s s' \<longleftrightarrow> r (snd s) (snd s')\<close>
  by (cases s, cases s', force)

(* TODO: write examples: (1) Arthur's nointerference, (2) observing local state *)

lemma sepimp_conj_step_mp:
  \<open>p \<le> p' \<Longrightarrow> (p' \<midarrow>\<^emph>\<^sub>\<and> q) \<^emph>\<and> p \<le> q\<close>
  by (meson order_refl sepimp_conj_mono sepimp_conj_sepconj_conj_shunt)

lemma comp2_exch4_over_rel_times[simp]:
  fixes ra :: \<open>'a \<Rightarrow> 'a \<Rightarrow> bool\<close>
    and rb :: \<open>'b \<Rightarrow> 'b \<Rightarrow> bool\<close>
  shows \<open>((ra \<times>\<^sub>R rb) \<times>\<^sub>R (rc \<times>\<^sub>R rd)) \<circ>\<^sub>2 exch4 = ((ra \<times>\<^sub>R rc) \<times>\<^sub>R (rb \<times>\<^sub>R rd))\<close>
  by (force simp add: comp_rel_def exch4_def rel_Times_def)

lemma example_observing_local_state:
  fixes F :: \<open>(('p \<rightharpoonup> 'v::perm_alg) \<times> ('p \<rightharpoonup> 'v)) \<times> ('h \<times> 'h) \<Rightarrow> bool\<close>
  assumes
    \<open>x \<noteq> y\<close>
  shows
    \<open>(=), (=) \<turnstile>\<^bsub>F \<midarrow>\<^emph>\<^sub>\<and> (\<bbbA> (\<lambda>(hl, hs). hl y) \<circ> exch4), F\<^esub>
    { (F \<midarrow>\<^emph>\<^sub>\<and> (\<bbbA> (\<lambda>(hl, hs). hl y) \<circ> exch4)) }
      liftC (\<langle>\<top>, (\<lambda>hl hl'. hl' = hl(x \<mapsto> v)) \<times>\<^sub>R (=)\<rangle>)
    { (F \<midarrow>\<^emph>\<^sub>\<and> (\<bbbA> (\<lambda>(hl, hs). hl y) \<circ> exch4)) }\<close>
  apply (simp add: liftC_def)
  apply (rule rgsat_atom[of _ _
        \<open>F \<midarrow>\<^emph>\<^sub>\<and> (\<bbbA> (\<lambda>(hl, hs). hl y) \<circ> exch4)\<close>
        \<open>F \<midarrow>\<^emph>\<^sub>\<and> (\<bbbA> (\<lambda>(hl, hs). hl y) \<circ> exch4)\<close>
        ])
        apply force
       apply force
      apply force
     apply force
    apply force
   apply clarsimp
   apply (clarsimp simp add: sp_def sepconj_conj_def sepimp_conj_def split: prod.splits)
  sorry


definition
  \<open>location_independent Pt \<equiv> \<lambda>(p,q).
    \<forall>h h' s s'.
      p (h, s) \<longrightarrow>
      q (h, s) (h', s') \<longrightarrow>
      (\<forall>\<sigma>.
        bij \<sigma> \<longrightarrow>
        (\<forall>\<rho>. \<rho> \<notin> Pt \<longrightarrow> \<sigma> \<rho> = \<rho>) \<longrightarrow>
        p (h \<circ> \<sigma>, s) \<and> q (h \<circ> \<sigma>, s) (h' \<circ> \<sigma>, s'))\<close>

definition
  \<open>value_independent Pt \<equiv> \<lambda>(p,q).
    \<forall>h h' s s'.
      p (h, s) \<longrightarrow>
      q (h, s) (h', s') \<longrightarrow>
      (\<forall>hx hx'.
        (\<forall>\<rho>. \<rho> \<notin> Pt \<longrightarrow> hx \<rho> = hx' \<rho>) \<longrightarrow>
        p (hx, s) \<and> q (hx, s) (hx', s'))\<close>

lemma example_deAmorim_noninterference:
  fixes S :: \<open>('p \<rightharpoonup> 'l::pre_perm_alg) \<times> 's \<Rightarrow> bool\<close>
  assumes
    \<open>r, g \<turnstile>\<^bsub>S, F\<^esub> { p } c { q }\<close>
    \<open>\<forall>p q.
        (p,q) \<in> all_atoms c \<longrightarrow>
        (\<forall>x x'. (S \<^emph>\<and> F) x \<longrightarrow> p x \<longrightarrow> q x x' \<longrightarrow>
          {\<rho>. fst x \<rho> \<noteq> fst x' \<rho>} \<subseteq> V)\<close>
  shows
    \<open>liftR r, liftR g \<turnstile>\<^bsub>\<bbbA> f \<circ> exch4, liftP F \<circ> exch4\<^esub> { liftP p \<circ> exch4 } liftC c { liftP q \<circ> exch4 }\<close>
  sorry

lemma opstep_all_atoms_antimono:
  \<open>sc \<midarrow>\<alpha>\<rightarrow> sc' \<Longrightarrow>
    sc = (s, c) \<Longrightarrow>
    sc' = (s', c') \<Longrightarrow>
    all_atoms c' \<le> all_atoms c\<close>
  apply (induct \<alpha> sc sc' arbitrary: s c s' c' rule: opstep.induct)
        apply force
       apply force
      apply force
     apply clarsimp
     apply (elim disjE conjE; clarsimp; blast)
    apply clarsimp
    apply (elim disjE conjE; clarsimp; blast)
   apply (clarsimp split: if_splits; fail)
  apply (clarsimp split: if_splits; fail)
  done


\<comment> \<open> note the instantiation of X to \<open>(FF \<midarrow>\<^emph>\<^sub>\<and> (\<bbbA> \<oo> \<circ> exch4))\<close> \<close>
lemma pred_preserved_then_pred_all_states:
  fixes c :: \<open>('l::pre_perm_alg \<times> 's) comm\<close>
  assumes
    \<open>safe n c z r g q S F\<close>
    \<open>z = s\<close>
    \<open>\<forall>s s'. ((=) \<times>\<^sub>R r) s s' \<longrightarrow> S s \<longrightarrow> X s \<longrightarrow> X s'\<close>
    \<open>\<forall>p q. (p, q) \<in> all_atoms c \<longrightarrow>
      (\<forall>hl hs hl' hs'.
        (\<forall>fl.
          hl ## fl \<longrightarrow> F (fl, hs) \<longrightarrow> hl' ## fl \<longrightarrow>
          p (hl + fl, hs) \<longrightarrow> q (hl + fl, hs) (hl' + fl, hs') \<longrightarrow>
          S (hl, hs) \<longrightarrow>
          X (hl, hs) \<longrightarrow> X (hl', hs')))\<close>
    \<open>X s\<close>
  shows
    \<open>safe n c z r g q X F\<close>
  using assms
proof (induct n c z r g q S F arbitrary: s rule: safe.induct)
  case (safe_nil S hl hs c r g q F)
  then show ?case by force
next
  case (safe_suc c q hl hs S r n g F)
  then show ?case
    apply (clarsimp simp add: safe_suc_iff eq_rtimes_R_iff top_rtimes_R_iff)
    apply (drule meta_spec2, drule meta_spec2, drule meta_mp, assumption,
        drule meta_mp, assumption, drule meta_mp, assumption)
    apply clarsimp
    apply (rule_tac x=hl' in exI)
    apply clarsimp
    apply (drule mp[of \<open>All _\<close>])
     apply (meson opstep_all_atoms_antimono subsetD; fail)
    apply clarsimp
    apply (erule opstep_act_cases, force)
    apply (frule vis_step_impl_atom)
    apply clarsimp
    apply (drule spec2, drule mp, rule set_mp[OF head_atoms_subseteq_all_atoms], assumption)
    apply metis
    done
qed


subsection \<open> Aaaaa \<close>

lemma pair_predicate_splitting:
  fixes P :: \<open>'a \<times> 'a \<Rightarrow> bool\<close>
  shows \<open>\<exists>p \<oo>::'a \<Rightarrow> 'v. P = \<lblot> p \<rblot> \<sqinter> \<bbbA> \<oo>\<close>
  nitpick[card 'a=2, card 'v=1]
  oops

definition uset where
  \<open>uset P \<equiv> \<lambda>x. {y. P (x,y)}\<close>

definition
  \<open>hyperset (r :: 'a \<times> 'a \<Rightarrow> bool) \<equiv>
    {A. \<exists>x. Ex (curry r x) \<and> A = {y. r (x,y)}}\<close>

definition
  \<open>hrelify (H :: 'a set set) \<equiv>
    \<lambda>(x,y). \<exists>A\<in>H. x\<in>A \<and> y\<in>A\<close>


lemma
  \<open>{} \<notin> H \<Longrightarrow>
    (\<forall>A\<in>H. \<forall>B\<in>H. (\<exists>x. x \<in> A\<inter>B) \<longrightarrow> A \<subseteq> B \<or> B \<subseteq> A) \<longleftrightarrow>
    (\<forall>A\<in>H. \<forall>B\<in>H. A \<subseteq> B \<longrightarrow> A = B)\<close>
  oops

lemma hyperset_hrelify_inverse:
  fixes H :: \<open>'a set set\<close>
  assumes \<open>{} \<notin> H\<close>
  assumes \<open>\<forall>A\<in>H. \<forall>B\<in>H. A \<subseteq> B \<longrightarrow> A = B\<close>
  assumes \<open>supcl H = H\<close>
  assumes ex_defining_member:
    \<open>\<forall>A\<in>H. \<exists>x\<in>A. \<forall>B\<in>H. x \<in> B \<longrightarrow> A \<subseteq> B\<close>
  shows \<open>hyperset (hrelify H) = H\<close>
  apply (simp add: hyperset_def hrelify_def)
  apply (rule set_eqI, rule iffI)
   apply clarsimp
   apply (rename_tac x y A)
   apply (rule subst[OF assms(3), of \<open>\<lambda>X. _ \<in> X\<close>])
   apply (clarsimp simp add: supcl_def)
   apply (rule_tac x=\<open>{A\<in>H. x\<in>A}\<close> in exI)
   apply blast
  apply clarsimp
  apply (rename_tac A)
  apply (cut_tac assms(1))
  apply (subgoal_tac \<open>\<exists>x. x \<in> A\<close>)
   prefer 2
   apply (simp add: ex_in_conv, blast)
  apply clarsimp
  apply (rule_tac
      Q=\<open>\<exists>x. A = {y. \<exists>B\<in>H. x \<in> B \<and> y \<in> B}\<close>
      in iffD1)
   apply blast
  apply (cut_tac ex_defining_member)
  apply (drule bspec, assumption)
  apply clarsimp
  apply (rename_tac a)
  apply (rule_tac x=a in exI)
  apply (rule iffD1[rotated, of \<open>Ball _ _\<close>], assumption)

  sorry

  apply (rule_tac x=x in exI)
  apply (rule Set.equalityI, force)
  apply clarsimp
  apply (rename_tac x y B)

  oops

lemma hrelify_hyperset_inverse:
  fixes r :: \<open>'a \<times> 'a \<Rightarrow> bool\<close>
  assumes \<open>quasireflp (curry r)\<close>
  assumes \<open>symp (curry r)\<close>
  shows \<open>hrelify (hyperset r) = r\<close>
  sledgehammer
  sorry


definition sec_obs (\<open>\<bbbO>\<close>) where
  \<open>sec_obs f \<equiv> \<lambda>(x,y). \<exists>X\<in>f x. \<exists>Y\<in>f y. X \<inter> Y \<noteq> {}\<close>

lemma pair_predicate_splitting:
  fixes P :: \<open>'a \<times> 'a \<Rightarrow> bool\<close>
  assumes \<open>quasireflp (curry P)\<close>
  assumes \<open>symp (curry P)\<close>
  shows \<open>P = \<bbbO> (\<lambda>x. {H. H = {x'. \<forall>y. P (x,y) \<longrightarrow> P (x',y)}})\<close>
  using assms
  apply (clarsimp simp add: fun_eq_iff uset_def sec_obs_def)
  apply (rule iffI)
   apply (clarsimp simp add: set_eq_iff symp_def)

  oops


section \<open> aaaa \<close>

lemma sec_agree_eq_mp:
  \<open>\<bbbA> (\<lambda>s. s x) \<sqinter> \<lblot> \<lambda>s. s x = s y \<rblot> \<le> \<bbbA> (\<lambda>s. s y)\<close>
  by (clarsimp simp add: sec_agree_def)

end