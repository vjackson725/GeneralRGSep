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

lemma comm_Times_rev[simp]:
  \<open>c \<times>\<^sub>C c = Skip \<longleftrightarrow> c = Skip\<close>
  \<open>c \<times>\<^sub>C c = ca' ;; cb' \<longleftrightarrow>
    (\<exists>ca cb. ca' = ca \<times>\<^sub>C ca \<and> cb' = cb \<times>\<^sub>C cb \<and> c = ca ;; cb)\<close>
  \<open>c \<times>\<^sub>C c = ca' \<parallel> cb' \<longleftrightarrow>
    (\<exists>ca cb. ca' = ca \<times>\<^sub>C ca \<and> cb' = cb \<times>\<^sub>C cb \<and> c = ca \<parallel> cb)\<close>
  \<open>c \<times>\<^sub>C c = ca' \<^bold>\<sqinter> cb' \<longleftrightarrow>
    (\<exists>ca cb. ca' = ca \<times>\<^sub>C ca \<and> cb' = cb \<times>\<^sub>C cb \<and> c = ca \<^bold>\<sqinter> cb)\<close>
  \<open>c \<times>\<^sub>C c = ca' \<^bold>\<box> cb' \<longleftrightarrow>
    (\<exists>ca cb. ca' = ca \<times>\<^sub>C ca \<and> cb' = cb \<times>\<^sub>C cb \<and> c = ca \<^bold>\<box> cb)\<close>
  \<open>c \<times>\<^sub>C c = DO c' OD \<longleftrightarrow> (\<exists>ca cb. c' = ca \<times>\<^sub>C ca \<and> c = DO ca OD)\<close>
  \<open>c \<times>\<^sub>C c = \<langle>r'\<rangle> \<longleftrightarrow> (\<exists>r. r' = r \<times>\<^sub>R r \<and> c = \<langle>r\<rangle>)\<close>
  by (induct c; clarsimp; argo)+


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

subsection \<open> Parallel Labels \<close>

datatype plabel = PL plabel | PR plabel | PHere

subsection \<open> Parallel-labelled actions \<close>

text \<open> Extended Actions \<close>

datatype aact =
  TauINdetL |
  TauINdetR |
  TauBasic | \<comment> \<open> Taus other than Taus from INdet \<close>
  AVis

text \<open>
  In an aact, a tau move may be buried under parallel synchronisation labels,
  or divided into an INdet Tau, which are handled separately by the evaluation semantics.
  In programs where sub-programs may take actions (\<box>), we need an
  inductive test for whether an action is internal, as the sub-program may be a parallel.
\<close>
definition \<open>tau_aact \<alpha> \<equiv> \<alpha> = TauBasic \<or> \<alpha> = TauINdetL \<or> \<alpha> = TauINdetR\<close>
definition \<open>vis_aact \<alpha> \<equiv> \<alpha> = AVis\<close>

lemma not_aact_iff:
  \<open>\<alpha> \<noteq> AVis \<longleftrightarrow> \<alpha> = TauBasic \<or> \<alpha> = TauINdetL \<or> \<alpha> = TauINdetR\<close>
  \<open>\<alpha> \<noteq> TauBasic \<longleftrightarrow> \<alpha> = AVis \<or> \<alpha> = TauINdetL \<or> \<alpha> = TauINdetR\<close>
  \<open>\<alpha> \<noteq> TauINdetL \<longleftrightarrow> \<alpha> = TauBasic \<or> \<alpha> = AVis \<or> \<alpha> = TauINdetR\<close>
  \<open>\<alpha> \<noteq> TauINdetR \<longleftrightarrow> \<alpha> = TauBasic \<or> \<alpha> = TauINdetL \<or> \<alpha> = AVis\<close>
  using aact.exhaust by blast+

lemma not_tau_aact_iff[simp]:
  \<open>\<not> tau_aact \<pi>\<alpha> \<longleftrightarrow> vis_aact \<pi>\<alpha>\<close>
  by (force simp add: tau_aact_def vis_aact_def not_aact_iff)

lemma not_vis_aact_iff[simp]:
  \<open>\<not> vis_aact \<pi>\<alpha> \<longleftrightarrow> tau_aact \<pi>\<alpha>\<close>
  using not_tau_aact_iff by blast

lemma vis_tau_aact_incompatible:
  \<open>vis_aact \<alpha> \<Longrightarrow> tau_aact \<alpha> = False\<close>
  \<open>tau_aact \<alpha> \<Longrightarrow> vis_aact \<alpha> = False\<close>
  by (simp add: tau_aact_def vis_aact_def not_aact_iff)+

lemma vis_aact_not_TauBasic[simp]:
  \<open>vis_aact \<alpha> \<Longrightarrow> \<alpha> = TauBasic \<longleftrightarrow> False\<close>
  \<open>vis_aact \<alpha> \<Longrightarrow> TauBasic = \<alpha> \<longleftrightarrow> False\<close>
  \<open>vis_aact (snd \<pi>\<alpha>) \<Longrightarrow> \<pi>\<alpha> = (\<pi>, TauBasic) \<longleftrightarrow> False\<close>
  by (force simp add: tau_aact_def vis_aact_def)+

lemma vis_aact_simps[simp]:
  \<open>vis_aact AVis\<close>
  \<open>vis_aact TauBasic \<longleftrightarrow> False\<close>
  \<open>vis_aact TauINdetL \<longleftrightarrow> False\<close>
  \<open>vis_aact TauINdetR \<longleftrightarrow> False\<close>
  by (simp add: vis_aact_def)+

lemma tau_aact_simps[simp]:
  \<open>tau_aact TauBasic\<close>
  \<open>tau_aact TauINdetL\<close>
  \<open>tau_aact TauINdetR\<close>
  \<open>tau_aact AVis \<longleftrightarrow> False\<close>
  by (simp add: tau_aact_def)+

lemma all_aact_or_iff[simp]:
  \<open>(\<forall>\<pi>\<alpha>. vis_aact \<pi>\<alpha> \<or> P \<pi>\<alpha>) \<longleftrightarrow> (\<forall>\<pi>\<alpha>. tau_aact \<pi>\<alpha> \<longrightarrow> P \<pi>\<alpha>)\<close>
  \<open>(\<forall>\<pi>\<alpha>. tau_aact \<pi>\<alpha> \<or> P \<pi>\<alpha>) \<longleftrightarrow> (\<forall>\<pi>\<alpha>. vis_aact \<pi>\<alpha> \<longrightarrow> P \<pi>\<alpha>)\<close>
  using not_tau_aact_iff by blast+

lemma all_tau_all_vis_iff:
  \<open>(\<forall>\<alpha>. tau_aact \<alpha> \<longrightarrow> P \<alpha>) \<and>
   (\<forall>\<alpha>. vis_aact \<alpha> \<longrightarrow> P \<alpha>) \<longleftrightarrow>
    All P\<close>
  by force

fun strip_aact where
  \<open>strip_aact AVis = Vis\<close>
| \<open>strip_aact _ = Tau\<close>

lemma strip_aact_rev_iff[simp]:
  \<open>strip_aact \<alpha> = Tau \<longleftrightarrow> tau_aact \<alpha>\<close>
  \<open>Tau = strip_aact \<alpha> \<longleftrightarrow> tau_aact \<alpha>\<close>
  \<open>strip_aact \<alpha> = Vis \<longleftrightarrow> vis_aact \<alpha>\<close>
  \<open>Vis = strip_aact \<alpha> \<longleftrightarrow> vis_aact \<alpha>\<close>
  unfolding tau_aact_def vis_aact_def
  by (metis act.distinct(1) not_aact_iff(4) strip_aact.simps)+


type_synonym 'a ptrace = \<open>(plabel \<times> aact) list\<close>


subsection \<open> Parallel Opstep \<close>

text \<open>
  Unfortunately, because acts are often universally quantified,
  using a general type variable becomes prohibitively unwieldy.
  (Due to \<open>itself\<close> types and schematics type vars in \<open>induct\<close>.)
  Thus we just use unit.
\<close>
fun aopstep :: \<open>plabel \<times> aact \<Rightarrow> 's pconfig \<Rightarrow> 's pconfig \<Rightarrow> bool\<close> where
  \<open>aopstep \<pi>\<alpha> (s, Skip) sc' \<longleftrightarrow> False\<close>
| \<open>aopstep \<pi>\<alpha> (s, ca ;; cb) sc' \<longleftrightarrow>
    \<pi>\<alpha> = (PHere, TauBasic) \<and> ca = Skip \<and> sc' = (s, cb) \<or>
    (\<exists>s' ca'. aopstep \<pi>\<alpha> (s, ca) (s', ca') \<and> sc' = (s', ca' ;; cb))\<close>
| \<open>aopstep \<pi>\<alpha> (s, ca \<^bold>\<sqinter> cb) sc' \<longleftrightarrow>
    \<pi>\<alpha> = (PHere, TauINdetL) \<and> sc' = (s, ca) \<or>
    \<pi>\<alpha> = (PHere, TauINdetR) \<and> sc' = (s, cb)\<close>
| \<open>aopstep \<pi>\<alpha> (s, ca \<^bold>\<box> cb) sc' \<longleftrightarrow>
    \<pi>\<alpha> = (PHere, TauBasic) \<and> ca = Skip \<and> sc' = (s, cb) \<or>
    \<pi>\<alpha> = (PHere, TauBasic) \<and> cb = Skip \<and> sc' = (s, ca) \<or>
    tau_aact (snd \<pi>\<alpha>) \<and> (\<exists>s' ca'. sc' = (s', ca' \<^bold>\<box> cb) \<and> aopstep \<pi>\<alpha> (s, ca) (s', ca')) \<or>
    tau_aact (snd \<pi>\<alpha>) \<and> (\<exists>s' cb'. sc' = (s', ca \<^bold>\<box> cb') \<and> aopstep \<pi>\<alpha> (s, cb) (s', cb')) \<or>
    vis_aact (snd \<pi>\<alpha>) \<and> aopstep \<pi>\<alpha> (s, ca) sc' \<or>
    vis_aact (snd \<pi>\<alpha>) \<and> aopstep \<pi>\<alpha> (s, cb) sc'\<close>
| \<open>aopstep \<pi>\<alpha> (s, ca \<parallel> cb) sc' \<longleftrightarrow>
    \<pi>\<alpha> = (PHere, TauBasic) \<and> ca = Skip \<and> cb = Skip \<and> sc' = (s, Skip) \<or>
    (\<exists>\<pi>\<alpha>' s' ca'. \<pi>\<alpha> = apfst PL \<pi>\<alpha>' \<and> aopstep \<pi>\<alpha>' (s, ca) (s', ca') \<and> sc' = (s', ca' \<parallel> cb)) \<or>
    (\<exists>\<pi>\<alpha>' s' cb'. \<pi>\<alpha> = apfst PR \<pi>\<alpha>' \<and> aopstep \<pi>\<alpha>' (s, cb) (s', cb') \<and> sc' = (s', ca \<parallel> cb'))\<close>
| \<open>aopstep \<pi>\<alpha> (s, DO c OD) sc' \<longleftrightarrow>
    \<pi>\<alpha> = (PHere, TauBasic) \<and> (\<forall>\<pi>\<alpha>' sc'. \<not> aopstep \<pi>\<alpha>' (s, c) sc') \<and> sc' = (s, Skip) \<or>
    (\<exists>s' c'. aopstep \<pi>\<alpha> (s, c) (s', c') \<and> sc' = (s', c' ;; DO c OD))\<close>
| \<open>aopstep \<pi>\<alpha> (s, \<langle>ar\<rangle>) sc' \<longleftrightarrow>
    (\<pi>\<alpha> = (PHere, AVis) \<and> ar s (fst sc') \<and> snd sc' = Skip)\<close>

lemmas aopstep_induct = aopstep.induct[case_names Skip Seq Indet Endet Par DoLoop Atom]


paragraph \<open> Pretty parallel operational semantics \<close>

text \<open> \<open>sc\<close> can step to \<open>sc'\<close> \<close>
abbreviation pretty_aopstep :: \<open>_ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> _\<close> (\<open>_ \<midarrow>(_)\<rightarrow>\<^sub>a _\<close> [60,0,60] 60) where
  \<open>sc \<midarrow>\<pi>\<alpha>\<rightarrow>\<^sub>a sc' \<equiv> aopstep \<pi>\<alpha> sc sc'\<close>

text \<open> no steps from \<open>sc\<close> can take place \<close>
abbreviation pretty_no_aopstep :: \<open>'s \<times> 's comm \<Rightarrow> bool\<close> (\<open>_ \<midarrow>'/\<rightarrow>\<^sub>a\<close> [60] 60) where
  \<open>sc \<midarrow>/\<rightarrow>\<^sub>a \<equiv> \<forall>\<pi>\<alpha> sc'. \<not> aopstep \<pi>\<alpha> sc sc'\<close>


subsubsection \<open> aopstep lemmas \<close>

lemma no_aopstep_rgstate_iff:
  \<open>sc \<midarrow>/\<rightarrow>\<^sub>a \<longleftrightarrow> (\<forall>\<alpha> l' s' c'. \<not> aopstep \<alpha> sc ((l', s'), c'))\<close>
  by clarsimp

lemma aopstep_iter_stepD:
  \<open>sc \<midarrow>\<pi>\<alpha>\<rightarrow>\<^sub>a sc' \<Longrightarrow>
    sc = (s, c) \<Longrightarrow>
    sc' = (s', c') \<Longrightarrow>
    (s, DO c OD) \<midarrow>\<pi>\<alpha>\<rightarrow>\<^sub>a (s', c' ;; DO c OD)\<close>
  by fastforce

lemma aopstep_tau_preserves_state:
  \<open>sc \<midarrow>\<pi>\<alpha>\<rightarrow>\<^sub>a sc' \<Longrightarrow> tau_aact (snd \<pi>\<alpha>) \<Longrightarrow> fst sc' = fst sc\<close>
  by (induct \<pi>\<alpha> sc sc' rule: aopstep_induct)
    (fastforce split: if_splits simp add: tau_aact_def)+

lemma vis_aopstep_impl_atom:
  \<open>sc \<midarrow>\<pi>\<alpha>\<rightarrow>\<^sub>a sc' \<Longrightarrow>
    vis_aact (snd \<pi>\<alpha>) \<Longrightarrow>
    \<exists>ar.
      ar \<in># head_atoms (snd sc) \<and>
      ar (fst sc) (fst sc')\<close>
  by (induct _ sc sc' rule: aopstep_induct; simp add: vis_aact_def tau_aact_def)
    fastforce+

lemma vis_aopstep_backwards_endet:
  \<open>sc \<midarrow>\<pi>\<alpha>\<rightarrow>\<^sub>a sc' \<Longrightarrow>
    vis_aact (snd \<pi>\<alpha>) \<Longrightarrow>
    snd sc' = ca' \<^bold>\<box> cb' \<Longrightarrow>
    \<exists>ca cb. snd sc = ca \<^bold>\<box> cb\<close>
  by (induct _ sc sc' arbitrary: ca' cb' rule: aopstep_induct)
    fastforce+

lemma aopstep_then_aopstep_right_seqD:
  \<open>sc \<midarrow>\<pi>\<alpha>\<rightarrow>\<^sub>a sc' \<Longrightarrow>
    sc = (s, c) \<Longrightarrow>
    sc' = (s', c') \<Longrightarrow>
    (s, c ;; cx) \<midarrow>\<pi>\<alpha>\<rightarrow>\<^sub>a (s', c' ;; cx)\<close>
  by (induct \<pi>\<alpha> sc sc' arbitrary: s c s' c' rule: aopstep_induct) simp+

lemma aopstep_then_aopstep_right_endetD:
  \<open>sc \<midarrow>\<pi>\<alpha>\<rightarrow>\<^sub>a sc' \<Longrightarrow>
    sc = (s, c) \<Longrightarrow>
    sc' = (s', c') \<Longrightarrow>
    (vis_aact (snd \<pi>\<alpha>) \<longrightarrow> (s, c \<^bold>\<box> cb) \<midarrow>\<pi>\<alpha>\<rightarrow>\<^sub>a (s', c')) \<and>
    (tau_aact (snd \<pi>\<alpha>) \<longrightarrow> (s, c \<^bold>\<box> cb) \<midarrow>\<pi>\<alpha>\<rightarrow>\<^sub>a (s', c' \<^bold>\<box> cb))\<close>
  by (induct \<pi>\<alpha> sc sc' arbitrary: s c s' c' rule: aopstep_induct)
    (simp add: vis_aact_def tau_aact_def)+

lemma aopstep_then_aopstep_left_endetD:
  \<open>sc \<midarrow>\<pi>\<alpha>\<rightarrow>\<^sub>a sc' \<Longrightarrow>
    sc = (s, c) \<Longrightarrow>
    sc' = (s', c') \<Longrightarrow>
    (vis_aact (snd \<pi>\<alpha>) \<longrightarrow> (s, ca \<^bold>\<box> c) \<midarrow>\<pi>\<alpha>\<rightarrow>\<^sub>a (s', c')) \<and>
    (tau_aact (snd \<pi>\<alpha>) \<longrightarrow> (s, ca \<^bold>\<box> c) \<midarrow>\<pi>\<alpha>\<rightarrow>\<^sub>a (s', ca \<^bold>\<box> c'))\<close>
  by (induct \<pi>\<alpha> sc sc' arbitrary: s c s' c' rule: aopstep_induct)
    (simp add: vis_aact_def tau_aact_def)+

lemma aopstep_aact_cases:
  \<open>sc \<midarrow>\<pi>\<alpha>\<rightarrow>\<^sub>a sc' \<Longrightarrow>
    (sc \<midarrow>\<pi>\<alpha>\<rightarrow>\<^sub>a sc' \<Longrightarrow> vis_aact (snd \<pi>\<alpha>) \<Longrightarrow> P) \<Longrightarrow>
    (sc \<midarrow>\<pi>\<alpha>\<rightarrow>\<^sub>a sc' \<Longrightarrow> tau_aact (snd \<pi>\<alpha>) \<Longrightarrow> fst sc' = fst sc \<Longrightarrow> P) \<Longrightarrow>
    P\<close>
  unfolding vis_aact_def tau_aact_def
  using not_vis_aact_iff aopstep_tau_preserves_state tau_aact_def vis_aact_def
  by blast

lemma aopstep_no_new_atoms:
  \<open>(s, c) \<midarrow>\<pi>\<alpha>\<rightarrow>\<^sub>a (ms', c') \<Longrightarrow> set_mset (all_atoms c') \<subseteq> set_mset (all_atoms c)\<close>
  by (induct c arbitrary: \<pi>\<alpha> c' ms')
    (fastforce split: if_splits)+

lemma aopstep_liftC_then_output_liftC:
  \<open>sscc \<midarrow>\<pi>\<alpha>\<rightarrow>\<^sub>a msscc' \<Longrightarrow>
    sscc = ((ll, ss), liftC c) \<Longrightarrow>
    msscc' = ((ll', ss'), cc') \<Longrightarrow>
    (\<exists>c'. cc' = liftC c')\<close>
  apply (induct _ sscc msscc' arbitrary: ll ss c ll' ss' cc' rule: aopstep_induct)
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
  \<open>sc \<midarrow>\<alpha>\<rightarrow> sc' \<Longrightarrow> \<exists>\<pi>\<alpha>. \<alpha> = strip_aact (snd \<pi>\<alpha>) \<and> sc \<midarrow>\<pi>\<alpha>\<rightarrow>\<^sub>a sc'\<close>
proof (induct \<alpha> sc sc' rule: opstep_induct)
  case (Endet \<alpha> s ca cb sc')
  then show ?case
    by (simp, (elim disjE; clarsimp simp add: tau_aact_def; metis))
next
  case (Par \<alpha> s ca cb sc')
  then show ?case
    by (simp, (elim disjE; clarsimp; metis))
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
  \<open>sc \<midarrow>\<pi>\<alpha>\<rightarrow>\<^sub>a sc' \<Longrightarrow> sc \<midarrow>strip_aact (snd \<pi>\<alpha>)\<rightarrow> sc'\<close>
proof (induct rule: aopstep_induct)
  case (Endet \<pi>\<alpha> s ca cb sc')
  then show ?case
    apply (cases \<open>snd \<pi>\<alpha>\<close>; simp)
       apply metis
      apply metis
     apply metis
    apply force
    done
next
  case (DoLoop \<pi>\<alpha> s c sc')
  then show ?case
    using opstep_then_aopstep
    apply (cases \<open>snd \<pi>\<alpha>\<close>; simp)
       apply fastforce
      apply fastforce
     apply clarsimp
     apply (metis prod.exhaust opstep_then_aopstep)
    apply fastforce
    done
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
  \<open>endet_expansion c c' \<Longrightarrow> (s, c) \<midarrow>\<pi>\<alpha>\<rightarrow>\<^sub>a (s', c') \<Longrightarrow> False\<close>
proof (induct c arbitrary: \<pi>\<alpha> c')
  case (Endet c1 c2)
  then show ?case
    by (clarsimp, metis comm.inject(4) eexp_reflI endet_expansion_right_EndetE
        endet_expansion_endet_leftD(1,2) endet_expansion_indet_left(7,8))
qed force+

lemmas self_aopstep_endet_cluster_then_crashD = 
  self_aopstep_endet_cluster_then_crash[rotated]

lemma self_aopstep_impossible[simp]:
  \<open>(s, c) \<midarrow>\<pi>\<alpha>\<rightarrow>\<^sub>a (s', c) = False\<close>
  \<open>(s, c1) \<midarrow>\<pi>\<alpha>\<rightarrow>\<^sub>a (s', c1 \<^bold>\<box> c2) = False\<close>
  \<open>(s, c2) \<midarrow>\<pi>\<alpha>\<rightarrow>\<^sub>a (s', c1 \<^bold>\<box> c2) = False\<close>
  by (force dest: self_aopstep_endet_cluster_then_crashD)+

lemma aopstep_endet_skip_then:
  \<open>(s, c \<^bold>\<box> Skip) \<midarrow>\<pi>\<alpha>\<rightarrow>\<^sub>a (s', c) \<Longrightarrow> tau_aact (snd \<pi>\<alpha>) \<and> s' = s\<close>
  \<open>(s, Skip \<^bold>\<box> c) \<midarrow>\<pi>\<alpha>\<rightarrow>\<^sub>a (s', c) \<Longrightarrow> tau_aact (snd \<pi>\<alpha>) \<and> s' = s\<close>
  by (simp, metis aopstep_tau_preserves_state split_pairs2 tau_aact_simps(1))+


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
  \<open>sc \<midarrow>\<rho>\<rightarrow>\<^sub>a\<^sup>* sc' \<Longrightarrow> list_all (tau_aact \<circ> snd) \<rho> \<Longrightarrow> fst sc' = fst sc\<close>
  by (induct rule: aopsteps.induct)
    (fastforce split: if_splits simp add: tau_aact_def dest: aopstep_tau_preserves_state)+

lemma aopsteps_rcons:
  \<open>sc \<midarrow>\<rho>\<rightarrow>\<^sub>a\<^sup>* sc' \<Longrightarrow>
    sc' \<midarrow>\<pi>\<alpha>\<rightarrow>\<^sub>a sc'' \<Longrightarrow>
    sc \<midarrow>\<rho> @ [\<pi>\<alpha>]\<rightarrow>\<^sub>a\<^sup>* sc''\<close>
  by (induct arbitrary: sc'' rule: aopsteps.induct)
   fastforce+

lemma aopsteps_iff:
  \<open>sc \<midarrow>\<rho>\<rightarrow>\<^sub>a\<^sup>* sc'' \<longleftrightarrow>
    \<rho> = [] \<and> sc'' = sc \<or>
    (\<exists>\<pi>\<alpha> \<rho>'. \<rho> = \<pi>\<alpha> # \<rho>' \<and> (\<exists>sc'. sc \<midarrow>\<pi>\<alpha>\<rightarrow>\<^sub>a sc' \<and> sc' \<midarrow>\<rho>'\<rightarrow>\<^sub>a\<^sup>* sc''))\<close>
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
  \<open>(s, c) \<midarrow>R, F, \<pi>\<alpha>e\<rightarrow>\<^sub>e\<^sub>a (s', c') \<Longrightarrow>
    (s, c \<parallel> cb) \<midarrow>R, F, map_eact (apfst PL) \<pi>\<alpha>e\<rightarrow>\<^sub>e\<^sub>a (s', c' \<parallel> cb)\<close>
  unfolding estep_def
  by (force split: prod.splits eact.splits)

lemma eastep_then_eastep_left_par:
  \<open>(s, c) \<midarrow>R, F, \<pi>\<alpha>e\<rightarrow>\<^sub>e\<^sub>a (s', c') \<Longrightarrow>
    (s, ca \<parallel> c) \<midarrow>R, F, map_eact (apfst PR) \<pi>\<alpha>e\<rightarrow>\<^sub>e\<^sub>a (s', ca \<parallel> c')\<close>
  unfolding estep_def
  by (force split: prod.splits eact.splits)

lemma eastep_then_eastep_right_endet:
  \<open>(s, c) \<midarrow>R, F, \<pi>\<alpha>e\<rightarrow>\<^sub>e\<^sub>a (s', c') \<Longrightarrow>
    (\<forall>\<pi>\<alpha>. \<pi>\<alpha>e = Env \<longrightarrow> (s, c \<^bold>\<box> cb) \<midarrow>R, F, \<pi>\<alpha>e\<rightarrow>\<^sub>e\<^sub>a (s', c' \<^bold>\<box> cb)) \<and>
    (\<forall>\<pi>\<alpha>. \<pi>\<alpha>e = Loc \<pi>\<alpha> \<longrightarrow>
      (vis_aact (snd \<pi>\<alpha>) \<longrightarrow> (s, c \<^bold>\<box> cb) \<midarrow>R, F, \<pi>\<alpha>e\<rightarrow>\<^sub>e\<^sub>a (s', c')) \<and>
      (tau_aact (snd \<pi>\<alpha>) \<longrightarrow> (s, c \<^bold>\<box> cb) \<midarrow>R, F, \<pi>\<alpha>e\<rightarrow>\<^sub>e\<^sub>a (s', c' \<^bold>\<box> cb)))\<close>
  unfolding estep_def
  by (force split: prod.splits simp add: vis_aact_def tau_aact_def)

lemma eastep_then_eastep_left_endet:
  \<open>(s, c) \<midarrow>R, F, \<pi>\<alpha>e\<rightarrow>\<^sub>e\<^sub>a (s', c') \<Longrightarrow>
    (\<forall>\<pi>\<alpha>. \<pi>\<alpha>e = Env \<longrightarrow> (s, ca \<^bold>\<box> c) \<midarrow>R, F, \<pi>\<alpha>e\<rightarrow>\<^sub>e\<^sub>a (s', ca \<^bold>\<box> c')) \<and>
    (\<forall>\<pi>\<alpha>. \<pi>\<alpha>e = Loc \<pi>\<alpha> \<longrightarrow>
      (vis_aact (snd \<pi>\<alpha>) \<longrightarrow> (s, ca \<^bold>\<box> c) \<midarrow>R, F, \<pi>\<alpha>e\<rightarrow>\<^sub>e\<^sub>a (s', c')) \<and>
      (tau_aact (snd \<pi>\<alpha>) \<longrightarrow> (s, ca \<^bold>\<box> c) \<midarrow>R, F, \<pi>\<alpha>e\<rightarrow>\<^sub>e\<^sub>a (s', ca \<^bold>\<box> c')))\<close>
  unfolding estep_def
  by (force split: prod.splits simp add: vis_aact_def tau_aact_def)

lemma estep_then_estep_doloop:
  \<open>(s, c) \<midarrow>R, F, \<pi>\<alpha>e\<rightarrow>\<^sub>e\<^sub>a (s', c') \<Longrightarrow>
    (\<forall>\<pi>\<alpha>. \<pi>\<alpha>e = Env \<longrightarrow> (s, DO c OD) \<midarrow>R, F, \<pi>\<alpha>e\<rightarrow>\<^sub>e\<^sub>a (s', DO c' OD)) \<and>
    (\<forall>\<pi>\<alpha>. \<pi>\<alpha>e = Loc \<pi>\<alpha> \<longrightarrow> (s, DO c OD) \<midarrow>R, F, \<pi>\<alpha>e\<rightarrow>\<^sub>e\<^sub>a (s', c' ;; DO c OD))\<close>
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
  \<open>((sxl, sxs), c) \<midarrow>\<pi>\<alpha>\<rightarrow>\<^sub>a (Inr (), cx') \<Longrightarrow>
    ((syl, sys), c) \<midarrow>\<pi>\<alpha>\<rightarrow>\<^sub>a (Inr (), cy') \<Longrightarrow>
    sec_head_determ c ((sxl, sxs), (syl, sys)) \<Longrightarrow>
    cx' = cy'\<close>
  apply (induct c arbitrary: sxl syl sxs sys cx' cy' \<pi>\<alpha>)
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
  \<open>((sxl, sxs), c) \<midarrow>\<pi>\<alpha>\<rightarrow>\<^sub>a (Inr (), c') \<Longrightarrow>
    ((syl, sys), c) \<midarrow>\<pi>\<alpha>\<rightarrow>\<^sub>a (Inr (), c') \<Longrightarrow>
    sec_head_determ c ((sxl, sxs), (syl, sys)) \<Longrightarrow>
    (((sxl, syl), (sxs, sys)), liftC c) \<midarrow>\<pi>\<alpha>\<rightarrow>\<^sub>a (Inr (), liftC c')\<close>
  apply (induct c arbitrary: sxl syl sxs sys c' \<pi>\<alpha>)
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
    \<open>\<forall>s' c'. \<not> ((sxl, sxs), c) \<midarrow>\<pi>\<alpha>\<rightarrow>\<^sub>a (s', c')\<close>
    \<open>\<forall>s' c'. \<not> ((syl, sys), c) \<midarrow>\<pi>\<alpha>\<rightarrow>\<^sub>a (s', c')\<close>
    \<open>tau_aact \<pi>\<alpha>\<close>
  shows
    \<open>\<forall>s' c'. \<not> (((sxl, syl), (sxs, sys)), liftC c) \<midarrow>\<pi>\<alpha>\<rightarrow>\<^sub>a (s', c')\<close>
  using assms
proof (induct c arbitrary: \<pi>\<alpha> sxl syl sxs sys)
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
  \<open>(\<pi>\<alpha> = TauBasic \<and> c1 = Skip \<and> syl' = syl \<and> sys' = sys \<and> c' = c2 \<or>
      \<pi>\<alpha> = TauBasic \<and> c2 = Skip \<and> syl' = syl \<and> sys' = sys \<and> c' = c1 \<or>
      (\<exists>c1'. c' = c1' \<^bold>\<box> c2 \<and> ((syl, sys), c1) \<midarrow>\<pi>\<alpha>\<rightarrow>\<^sub>a ((syl', sys'), c1')) \<or>
      (\<exists>c2'. c' = c1 \<^bold>\<box> c2' \<and> ((syl, sys), c2) \<midarrow>\<pi>\<alpha>\<rightarrow>\<^sub>a ((syl', sys'), c2'))) \<and>
    (\<pi>\<alpha> = TauBasic \<and> c1 = Skip \<and> sxl' = sxl \<and> sxs' = sxs \<and> c' = c2 \<or>
      \<pi>\<alpha> = TauBasic \<and> c2 = Skip \<and> sxl' = sxl \<and> sxs' = sxs \<and> c' = c1 \<or>
      (\<exists>c1'. c' = c1' \<^bold>\<box> c2 \<and> ((sxl, sxs), c1) \<midarrow>\<pi>\<alpha>\<rightarrow>\<^sub>a ((sxl', sxs'), c1')) \<or>
      (\<exists>c2'. c' = c1 \<^bold>\<box> c2' \<and> ((sxl, sxs), c2) \<midarrow>\<pi>\<alpha>\<rightarrow>\<^sub>a ((sxl', sxs'), c2'))) \<longleftrightarrow>
    (\<exists>c1'. c' = c1' \<^bold>\<box> c2 \<and>
      ((syl, sys), c1) \<midarrow>\<pi>\<alpha>\<rightarrow>\<^sub>a ((syl', sys'), c1') \<and>
      ((sxl, sxs), c1) \<midarrow>\<pi>\<alpha>\<rightarrow>\<^sub>a ((sxl', sxs'), c1')) \<or>
    (\<exists>c2'. c' = c1 \<^bold>\<box> c2' \<and>
      ((syl, sys), c2) \<midarrow>\<pi>\<alpha>\<rightarrow>\<^sub>a ((syl', sys'), c2') \<and>
      ((sxl, sxs), c2) \<midarrow>\<pi>\<alpha>\<rightarrow>\<^sub>a ((sxl', sxs'), c2')) \<or>
    (\<pi>\<alpha> = TauBasic \<and> c1 = Skip \<and> c2 = c' \<or>
      \<pi>\<alpha> = TauBasic \<and> c1 = c' \<and> c2 = Skip) \<and>
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
  \<open>(sx, c) \<midarrow>\<pi>\<alpha>\<rightarrow>\<^sub>a (sx', cx') \<Longrightarrow>
    (sy, c) \<midarrow>\<pi>\<alpha>\<rightarrow>\<^sub>a (sy', cy') \<Longrightarrow>
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
  \<open>(sx, c) \<midarrow>\<pi>\<alpha>\<rightarrow>\<^sub>a (sx', c') \<Longrightarrow>
    (sy, c) \<midarrow>\<pi>\<alpha>\<rightarrow>\<^sub>a (sy', c') \<Longrightarrow>
    sec_head_determ c (sx, sy) \<Longrightarrow>
    (((fst sx, fst sy), (snd sx, snd sy)), liftC c)
      \<midarrow>\<pi>\<alpha>\<rightarrow>\<^sub>a (((fst sx', fst sy'), (snd sx', snd sy')), liftC c')\<close>
  apply (induct c arbitrary: sx sy sx sy c' \<pi>\<alpha>)
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
    apply (subgoal_tac \<open>\<pi>\<alpha> \<noteq> TauBasic\<close>)
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
  \<open>(sx, c) \<midarrow>\<pi>\<alpha>\<rightarrow>\<^sub>a (sx', c') \<Longrightarrow>
    (sy, c) \<midarrow>\<pi>\<alpha>\<rightarrow>\<^sub>a (sy', c') \<Longrightarrow>
    sec_head_determ c (sx, sy) \<Longrightarrow>
    (((fst sx, fst sy), (snd sx, snd sy)), liftC c)
      \<midarrow>\<pi>\<alpha>\<rightarrow>\<^sub>a (((fst sx', fst sy'), (snd sx', snd sy')), liftC c')\<close>
  apply (induct c arbitrary: sx sy sx sy c' \<pi>\<alpha>)
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
    apply (subgoal_tac \<open>\<pi>\<alpha> \<noteq> TauBasic\<close>)
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
  Unfortunately dependent on the state the command is executed in, because of loops.
\<close>
definition basic_tau_reducts :: \<open>'l \<times> 's \<Rightarrow> ('l \<times> 's) comm \<Rightarrow> ('l \<times> 's) comm set\<close> where
  \<open>basic_tau_reducts s c \<equiv>
    {c'. \<exists>\<rho> s'.
      (s, c) \<midarrow>\<rho>\<rightarrow>\<^sub>a\<^sup>* (s', c') \<and>
      list_all ((=) TauBasic \<circ> snd) \<rho> \<and>
      ((\<exists>\<pi>\<alpha> s'' c''. (s', c') \<midarrow>\<pi>\<alpha>\<rightarrow>\<^sub>a (s'', c'') \<and> TauBasic \<noteq> snd \<pi>\<alpha>) \<or>
        (s', c') \<midarrow>/\<rightarrow>\<^sub>a)}\<close>


lemma btr_seq_left[intro]:
  assumes
    \<open>ca' \<in> basic_tau_reducts s ca\<close>
    \<open>ca' \<noteq> Skip\<close>
  shows
    \<open>ca' ;; cb \<in> basic_tau_reducts s (ca ;; cb)\<close>
  using assms
proof (clarsimp simp add: basic_tau_reducts_def simp del: split_paired_Ex)
  fix s' c' \<rho> s'' \<pi>\<alpha>
  assume assms2:
    \<open>(s, ca) \<midarrow>\<rho>\<rightarrow>\<^sub>a\<^sup>* (s', c')\<close>
    \<open>list_all ((=) TauBasic \<circ> snd) \<rho>\<close>
    \<open>TauBasic \<noteq> snd \<pi>\<alpha>\<close>
    \<open>(s', c') \<midarrow>\<pi>\<alpha>\<rightarrow>\<^sub>a (s'', ca')\<close>
  moreover then have
    \<open>(s, ca ;; cb) \<midarrow>\<rho>\<rightarrow>\<^sub>a\<^sup>* (s', c' ;; cb)\<close>
    apply (induct \<rho> arbitrary: ca ca')
     apply force
    apply (rename_tac \<alpha> \<rho> ca ca')
    apply clarsimp
    apply (rename_tac slx ssx cx)
    oops


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
inductive_cases btr_atomE[elim!]: \<open>basic_tau_reducts s \<langle>ar\<rangle> c'\<close>
*)

lemma btr_skip_left_iff[simp]:
  \<open>c' \<in> basic_tau_reducts s Skip \<longleftrightarrow> c' = Skip\<close>
  unfolding basic_tau_reducts_def
  oops

lemma basic_tau_reducts_from_basic_tau_step:
  \<open>sc \<midarrow>\<pi>\<alpha>\<rightarrow>\<^sub>a sc' \<Longrightarrow>
    snd sc' \<in> basic_tau_reducts (fst sc) (snd sc) \<Longrightarrow>
    fst sc' = fst sc \<and> basic_tau_aact (snd \<pi>\<alpha>)\<close>
  apply (induct \<pi>\<alpha> sc sc' rule: aopstep_induct)
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
  apply (metis aopsteps_nil list_all_simps(2) surjective_pairing)
  done

lemma basic_tau_reducts_step_trans:
  \<open>(s, c) \<midarrow>\<pi>\<alpha>\<rightarrow>\<^sub>a (s', c') \<Longrightarrow>
    basic_tau_aact (snd \<pi>\<alpha>) \<Longrightarrow>
    c'' \<in> basic_tau_reducts s' c' \<Longrightarrow>
    c'' \<in> basic_tau_reducts s c\<close>
  apply (clarsimp simp add: basic_tau_reducts_def)
  oops

lemma basic_tau_aact_exclusive:
  \<open>sc \<midarrow>\<pi>\<alpha>\<rightarrow>\<^sub>a sc' \<Longrightarrow>
    TauBasic = snd \<pi>\<alpha> \<Longrightarrow>
    sc \<midarrow>\<pi>\<alpha>'\<rightarrow>\<^sub>a sc' \<Longrightarrow>
    TauBasic = snd \<pi>\<alpha>'\<close>
  apply (frule aopstep_tau_preserves_state, force)
  apply (induct \<pi>\<alpha> sc sc' arbitrary: \<pi>\<alpha>' rule: aopstep.induct)
        apply force
       apply force
      apply force
    (* endet *)
     apply (clarsimp simp add: if_bool_eq_disj)
     apply (rename_tac s' c' \<alpha>')
     apply (case_tac \<open>ca = Skip \<and> cb = Skip\<close>)
      apply force
     apply (clarsimp simp add: vis_tau_aact_incompatible(2))
  subgoal sorry
      (* par *)
    apply clarsimp
  subgoal sorry
      (* do-loop *)
  subgoal sorry
      (* atom *)
  apply force
  oops

lemma basic_tau_reducts_from_basic_tau_exec:
  \<open>sc \<midarrow>\<rho>\<rightarrow>\<^sub>a\<^sup>* sc' \<Longrightarrow>
    sc \<midarrow>\<rho>'\<rightarrow>\<^sub>a\<^sup>* sc' \<Longrightarrow>
    list_all (basic_tau_aact \<circ> snd) \<rho>' \<Longrightarrow>
    length \<rho> \<le> length \<rho>' \<Longrightarrow>
    fst sc' = fst sc \<and> list_all (basic_tau_aact \<circ> snd) \<rho>\<close>
  apply (induct arbitrary: \<rho>' rule: aopsteps.induct)
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
  \<open>sscc \<midarrow>\<pi>\<alpha>\<rightarrow>\<^sub>a msscc' \<Longrightarrow>
    sscc = ((ll, ss), liftC c) \<Longrightarrow>
    msscc' = ((ll', ss'), cc') \<Longrightarrow>
    ((fst ll, fst ss), c) \<midarrow>\<pi>\<alpha>\<rightarrow>\<^sub>a ((fst ll', fst ss'), unliftC cc')\<close>
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
  \<open>sscc \<midarrow>\<pi>\<alpha>\<rightarrow>\<^sub>a msscc' \<Longrightarrow>
    sscc = ((ll, ss), liftC c) \<Longrightarrow>
    msscc' = ((ll', ss'), cc') \<Longrightarrow>
    ((snd ll, snd ss), c) \<midarrow>\<pi>\<alpha>\<rightarrow>\<^sub>a ((snd ll', snd ss'), unliftC cc')\<close>
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
    \<open>sfsfcc \<midarrow>\<pi>\<alpha>\<rightarrow>\<^sub>a sfsfcc'\<close>
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
    \<open>((fst sx + fx, snd sx), c) \<midarrow>\<pi>\<alpha>\<rightarrow>\<^sub>a ((fst sx' + fx, snd sx'), unliftC cc')\<close>
    using assms
    apply clarsimp
    apply (frule double_aopstep_implies_fst_opstep, fast, fast, simp)
    done
  moreover have right_step:
    \<open>((fst sy + fy, snd sy), c) \<midarrow>\<pi>\<alpha>\<rightarrow>\<^sub>a ((fst sy' + fy, snd sy'), unliftC cc')\<close>
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
          \<midarrow>\<pi>\<alpha>\<rightarrow>\<^sub>a (((fst sx' + fx, fst sy' + fy), snd sx', snd sy'), liftC' cx' cy'))\<close>
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
    apply (rename_tac sx' c' ly' sy' \<gamma>\<gamma>s' fx fy \<tau>xs cx' \<pi>\<alpha>x lx' \<tau>ys cy' \<pi>\<alpha>y)
    apply (clarsimp simp add: safe_suc_iff)
    apply (subgoal_tac \<open>\<pi>\<alpha>y = \<pi>\<alpha>x\<close>)
     prefer 2 (* TODO: not true *)
    subgoal sorry
    apply (subgoal_tac \<open>cx' = cy'\<close>)
     prefer 2 (* TODO: not true *)
    subgoal sorry
    apply clarsimp
    apply (frule(1) double_stepI[where sxs=sxs and sys=sys])
     apply (clarsimp simp add: pred_executions_suc_iff le_fun_def sepconj_conjI)
    subgoal sorry
    apply (drule_tac x=\<open>strip_aact \<pi>\<alpha>x\<close> in spec, drule spec2, drule spec2,
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
      curr_cfg \<rho> \<midarrow>\<pi>\<alpha>\<rightarrow>\<^sub>a (s', c') \<Longrightarrow>
      (CTrStep (s', c') (Loc \<alpha>) \<rho>, Running) \<in> cfg_traces sc\<close>
| cfg_traces_crash[intro!]:
    \<open>(\<rho>, Running) \<in> cfg_traces sc \<Longrightarrow>
      \<exists>\<alpha> c'. curr_cfg \<rho> \<midarrow>\<pi>\<alpha>\<rightarrow>\<^sub>a (Inr (), c') \<Longrightarrow>
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

definition
  \<open>nonsync_aact \<alpha> \<equiv> \<alpha> = TauBasic \<or> \<alpha> = AVis\<close>

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
        ((sx, cx), (sy, cy))
        ((sx', cx), (sy', cy))\<close>
| dstep_conf_step_left[intro]:
  \<open>\<exists>fy. FF ((fx,fy),(snd sx, snd sy)) \<and> fst sy ## fy \<Longrightarrow>
    nonsync_aact \<alpha> \<Longrightarrow>
    \<comment> \<open> left step \<close>
    fst sx ## fx \<Longrightarrow>
    ((fst sx + fx, snd sx), cx) \<midarrow>\<pi>\<alpha>\<rightarrow>\<^sub>a ((fst sx' + fx, snd sx'), cx') \<Longrightarrow>
    dstep_conf RR FF ([Loc \<alpha>], [])
      ((sx, cx), (sy, cy))
      ((sx', cx'), (sy, cy))\<close>
| dstep_conf_step_right[intro]:
  \<open>\<exists>fx. FF ((fx,fy),(snd sx, snd sy)) \<and> fst sx ## fx \<Longrightarrow>
    nonsync_aact \<alpha> \<Longrightarrow>
    \<comment> \<open> right step \<close>
    fst sy ## fy \<Longrightarrow>
    ((fst sy + fy, snd sy), cy) \<midarrow>\<pi>\<alpha>\<rightarrow>\<^sub>a ((fst sy' + fy, snd sy'), cy') \<Longrightarrow>
    dstep_conf RR FF ([], [Loc \<alpha>])
      ((sx, cx), (sy, cy))
      ((sx, cx), (sy', cy'))\<close>
| dstep_conf_local[intro]:
  \<open>FF ((fx,fy),(snd sx, snd sy)) \<Longrightarrow>
    \<not> nonsync_aact \<alpha> \<Longrightarrow>
    \<comment> \<open> left steps \<close>
    fst sx ## fx \<Longrightarrow>
    ((fst sx + fx, snd sx), cx) \<midarrow>\<pi>\<alpha>\<rightarrow>\<^sub>a ((fst sx' + fx, snd sx'), cx') \<Longrightarrow>
    \<comment> \<open> right steps \<close>
    fst sx ## fx \<Longrightarrow>
    ((fst sy + fy, snd sy), cy) \<midarrow>\<pi>\<alpha>\<rightarrow>\<^sub>a ((fst sy' + fy, snd sy'), cy') \<Longrightarrow>
    dstep_conf RR FF ([Loc \<alpha>], [Loc \<alpha>])
      ((sx, cx), (sy, cy))
      ((sx', cx'), (sy', cy'))\<close>

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
        ((sx, cx), (sy, cy))
        ((sx', cx), (sy', cy))\<close>
  | dstep_secure_btau_left[intro]:
    \<comment> \<open> a process may left-step if it's a basic tau move. \<close>
    \<open>\<exists>fy. FF ((fx,fy),(snd sx, snd sy)) \<and> fst sy ## fy \<Longrightarrow>
    basic_tau_aact \<alpha> \<Longrightarrow>
    \<comment> \<open> left step \<close>
    fst sx ## fx \<Longrightarrow>
    ((fst sx + fx, snd sx), cx) \<midarrow>\<pi>\<alpha>\<rightarrow>\<^sub>a ((fst sx' + fx, snd sx'), cx') \<Longrightarrow>
    dstep_secure RR FF ([Loc \<alpha>], [])
      ((sx, cx), (sy, cy))
      ((sx', cx), (sy, cy'))\<close>
  | dstep_secure_btau_right[intro]:
    \<comment> \<open> a process may right-step if it's a basic tau move. \<close>
    \<open>\<exists>fx. FF ((fx,fy),(snd sx, snd sy)) \<and> fst sx ## fx \<Longrightarrow>
    basic_tau_aact \<alpha> \<Longrightarrow>
    \<comment> \<open> right step \<close>
    fst sy ## fy \<Longrightarrow>
    ((fst sy + fy, snd sy), cy) \<midarrow>\<pi>\<alpha>\<rightarrow>\<^sub>a ((fst sy' + fy, snd sy'), cy') \<Longrightarrow>
    dstep_secure RR FF ([], [Loc \<alpha>])
      ((sx, cx), (sy, cy))
      ((sx, cx), (sy', cy'))\<close>
  | dstep_secure_local[intro]:
    \<comment> \<open> all other steps must be synchronised to be secure. \<close>
    \<open>FF ((fx,fy),(snd sx, snd sy)) \<Longrightarrow>
    \<not> basic_tau_aact \<alpha> \<Longrightarrow>
    \<comment> \<open> left steps \<close>
    fst sx ## fx \<Longrightarrow>
    ((fst sx + fx, snd sx), cx) \<midarrow>\<pi>\<alpha>\<rightarrow>\<^sub>a ((fst sx' + fx, snd sx'), cx') \<Longrightarrow>
    \<comment> \<open> right steps \<close>
    fst sx ## fx \<Longrightarrow>
    ((fst sy + fy, snd sy), cy) \<midarrow>\<pi>\<alpha>\<rightarrow>\<^sub>a ((fst sy' + fy, snd sy'), cy') \<Longrightarrow>
    dstep_secure RR FF ([Loc \<alpha>], [Loc \<alpha>])
      ((sx, cx), (sy, cy))
      ((sx', cx'), (sy', cy'))\<close>

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
    \<open>ss = ((sx, cx), (sy, cy)) \<Longrightarrow>
      ss' = ((sx', cx), (sy', cy)) \<Longrightarrow>
      R (snd sx, snd sy) (snd sx', snd sy') \<Longrightarrow>
      fst sx' = fst sx \<Longrightarrow>
      fst sy' = fst sy \<Longrightarrow>
      dstep_exact R F ([Env], [Env]) ss ss'\<close>
| dstep_exact_local[intro]:
  \<comment> \<open> all other steps must be synchronised to be secure. \<close>
  \<open>ss = (((slx, ssx), cx), ((sly, ssy), cy)) \<Longrightarrow>
    ss' = (((slx', ssx'), cx'), ((sly', ssy'), cy')) \<Longrightarrow>
    F ((fx, fy), (ssx, ssy)) \<Longrightarrow>
    \<comment> \<open> left steps \<close>
    slx ## fx \<Longrightarrow>
    ((slx + fx, ssx), cx) \<midarrow>\<pi>\<alpha>\<rightarrow>\<^sub>a ((slx' + fx, ssx'), cx') \<Longrightarrow>
    \<comment> \<open> right steps \<close>
    slx ## fx \<Longrightarrow>
    ((sly + fy, ssy), cy) \<midarrow>\<pi>\<alpha>\<rightarrow>\<^sub>a ((sly' + fy, ssy'), cy') \<Longrightarrow>
    dstep_exact R F ([Loc \<pi>\<alpha>], [Loc \<pi>\<alpha>]) scsc scsc'\<close>

inductive_cases dstep_exact_nilLE[elim!]: \<open>dstep_exact R F ([], Y) ss zz'\<close>
inductive_cases dstep_exact_nilRE[elim!]: \<open>dstep_exact R F (X, []) ss zz'\<close>
inductive_cases dstep_exact_EnvXE[elim!]: \<open>dstep_exact R F (Env#\<rho>x, X) ss zz'\<close>
inductive_cases dstep_exact_XEnvE[elim!]: \<open>dstep_exact R F (X, Env#\<rho>y) ss zz'\<close>
inductive_cases dstep_exact_LocXE[elim]: \<open>dstep_exact R F (Loc \<alpha>x#\<rho>x, X) ss zz'\<close>
inductive_cases dstep_exact_XLocE[elim]: \<open>dstep_exact R F (X, Loc \<alpha>y#\<rho>y) ss zz'\<close>

abbreviation dstep_exact_pretty :: \<open>_ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> bool\<close>
  (\<open>_ =_, _, _\<Rightarrow>\<^sub>\<E> _\<close> [50, 0, 0, 0, 50])
  where
    \<open>ss =R, F, \<rho>xy\<Rightarrow>\<^sub>\<E> ss' \<equiv> dstep_exact R F \<rho>xy ss ss'\<close>

lemma dstep_exact_env_iff:
  \<open>ss =R, F, ([Env], [Env])\<Rightarrow>\<^sub>\<E> ss' \<longleftrightarrow>
    (\<exists>sx kx cx sy ky cy sx' sy'.
      ss = ((sx, cx), (sy, cy)) \<and>
      ss' = ((sx', cx), (sy', cy)) \<and>
      R (snd sx, snd sy) (snd sx', snd sy') \<and>
      fst sx' = fst sx \<and>
      fst sy' = fst sy)\<close>
  by fastforce

lemma dstep_exact_loc_iff:
  fixes scsc :: \<open>(('l::pre_perm_alg \<times> 's) \<times> _ comm) \<times> (('l::pre_perm_alg \<times> 's) \<times> _ comm)\<close>
  shows
  \<open>scsc =R, F, ([Loc \<pi>\<alpha>x], [Loc \<pi>\<alpha>y])\<Rightarrow>\<^sub>\<E> scsc' \<longleftrightarrow>
    \<pi>\<alpha>x = \<pi>\<alpha>y \<and>
    (\<exists>fx fy.
      F ((fx, fy), (snd (fst (fst scsc)), snd (fst (snd scsc)))) \<and>
      fst (fst (fst scsc)) ## fx \<and>
      ((fst (fst (fst scsc)) + fx, snd (fst (fst scsc))), snd (fst scsc))
        \<midarrow>\<pi>\<alpha>x\<rightarrow>\<^sub>a
        ((fst (fst (fst scsc')) + fx, snd (fst (fst scsc'))), snd (fst scsc')) \<and>
      fst (fst (snd scsc)) ## fy \<and>
      ((fst (fst (snd scsc)) + fy, snd (fst (snd scsc))), snd (snd scsc))
        \<midarrow>\<pi>\<alpha>y\<rightarrow>\<^sub>a
        ((fst (fst (snd scsc')) + fy, snd (fst (snd scsc'))), snd (snd scsc')))\<close>
  apply (cases scsc, cases scsc', clarsimp)
  apply safe
    apply blast
   apply (elim dstep_exact.cases)
    apply blast
   apply clarsimp

  sorry


subsection \<open> Double Executions \<close>

(* Note: appends to the end *)
inductive dexec
  :: \<open>(_ list \<times> _ list \<Rightarrow>
        ('s \<times> 'sb comm) \<times> ('s \<times> 'sb comm) \<Rightarrow>
        ('s \<times> 'sb comm) \<times> ('s \<times> 'sb comm) \<Rightarrow>
        bool) \<Rightarrow>
      (_ \<Rightarrow> _ \<Rightarrow> bool) \<Rightarrow>
      (_ \<Rightarrow> _ \<Rightarrow> bool) \<Rightarrow>
      _ list \<times> _ list \<Rightarrow>
      ('s \<times> 'sb comm) \<times> ('s \<times> 'sb comm) \<Rightarrow>
      ('s \<times> 'sb comm) \<times> ('s \<times> 'sb comm) \<Rightarrow>
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


definition \<open>secstate_bridge I \<equiv> \<lambda>sx sy. I (exch4 (sx, sy))\<close>

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
   apply (clarsimp, metis dstep_exact_env fst_conv snd_conv)
  apply fastforce
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

lemma empty_rely_no_env_estep:
  \<open>sc \<midarrow>F, \<bottom>, \<alpha>e\<rightarrow>\<^sub>e\<^sub>a sc' \<Longrightarrow>
    \<exists>\<alpha>. \<alpha>\<^sub>e = Loc \<alpha>\<close>
  by (cases \<alpha>e) force+

lemma empty_rely_no_env_esteps:
  \<open>sc \<midarrow>R, F, \<rho>e\<rightarrow>\<^sub>e\<^sub>a\<^sup>* sc' \<Longrightarrow>
    R = \<bottom> \<Longrightarrow>
    list_all (\<lambda>\<alpha>e. \<exists>\<alpha>. \<alpha>e = Loc \<alpha>) \<rho>e\<close>
  by (induct rule: easteps_induct) force+

(*
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
        (\<exists>\<alpha> s''. (s', c') \<midarrow>\<pi>\<alpha>\<rightarrow>\<^sub>a (s'', c'') \<and> \<not> basic_tau_aact \<alpha>)}\<close>

definition btau_equiv
  :: \<open>('l::pre_perm_alg \<times> 's \<Rightarrow> bool) \<Rightarrow>
        ('l::pre_perm_alg \<times> 's) config \<Rightarrow> ('l \<times> 's) config \<Rightarrow> bool\<close>
  where
    \<open>btau_equiv FF sca scb \<equiv> sync_set FF sca = sync_set FF scb\<close>
*)

lemma dexec_trans:
  \<open>ss' =step, L, C, \<rho>\<rho>'\<Rightarrow>\<^sup>* ss'' \<Longrightarrow>
    ss =step, L, C, \<rho>\<rho>\<Rightarrow>\<^sup>* ss' \<Longrightarrow>
    ss =step, L, C, (fst \<rho>\<rho> @ fst \<rho>\<rho>', snd \<rho>\<rho> @ snd \<rho>\<rho>')\<Rightarrow>\<^sup>* ss''\<close>
  apply (induct rule: dexec.inducts)
   apply force
  apply (clarsimp, metis append.assoc dexec_step fst_conv snd_conv)
  done


subsubsection \<open> Aopstep lemmas \<close>

lemma baopsteps_tau_preserves_state:
  \<open>sc \<midarrow>\<rho>\<rightarrow>\<^sub>a\<^sup>* sc' \<Longrightarrow>
    list_all ((=) TauBasic \<circ> snd) \<rho> \<Longrightarrow>
    fst sc' = fst sc\<close>
  by (simp add: aopsteps_tau_preserves_state list.pred_set)

lemma tau_aopstep_state_irrelevant:
  \<comment> \<open> False because of do loops \<close>
  \<open>sc \<midarrow>\<pi>\<alpha>\<rightarrow>\<^sub>a sc' \<Longrightarrow>
    tau_aact (snd \<pi>\<alpha>) \<Longrightarrow>
    (sx, snd sc) \<midarrow>\<pi>\<alpha>\<rightarrow>\<^sub>a (sx, snd sc')\<close>
  apply (induct _ sc sc' arbitrary: sx rule: aopstep_induct)
        apply force
       apply force
      apply force
     apply clarsimp
     apply (metis not_tau_aact_iff)
    apply force
  subgoal sorry
  apply force
  oops

lemma btau_astep_preserves_nextstep:
  assumes
    \<open>sc \<midarrow>\<pi>\<alpha>\<rightarrow>\<^sub>a sc'\<close>
    \<open>TauBasic = snd \<pi>\<alpha>\<close>
    \<open>sc \<midarrow>\<pi>\<alpha>x\<rightarrow>\<^sub>a scx\<close>
    \<open>\<pi>\<alpha>x \<noteq> \<pi>\<alpha>\<close>
  shows
    \<open>\<exists>cx'. sc' \<midarrow>\<pi>\<alpha>x\<rightarrow>\<^sub>a (fst scx, cx')\<close>
proof -
  have H1: \<open>fst sc = fst sc'\<close>
    using assms(1-2)
    by (simp add: aopstep_tau_preserves_state)
  
  show ?thesis
    using assms H1
  proof (induct _ sc sc' arbitrary: \<pi>\<alpha>x scx rule: aopstep_induct)
    case (Seq \<pi>\<alpha> s ca cb sc')
    then show ?case
      apply clarsimp
      apply (metis aopstep.simps(1) aopstep_then_aopstep_right_seqD fst_conv
          prod.exhaust)
      done
  next
    case (Endet \<pi>\<alpha> s ca cb sc')
    show ?case
      using Endet.prems
      apply (cases scx, rename_tac sx cx)
      apply (clarsimp simp add: vis_tau_aact_incompatible(2))
      apply (elim disjE[of \<open>\<pi>\<alpha> = _ \<and> _\<close>])
        apply fastforce
       apply fastforce
      apply (elim disjE[of \<open>\<pi>\<alpha>x = _ \<and> _\<close>])
        apply (clarsimp, blast)
       apply (clarsimp, blast)
      apply (case_tac \<open>
        ((\<exists>s' ca'. sc' = (s', ca' \<^bold>\<box> cb)) \<or> (\<exists>s' cb'. sc' = (s', ca \<^bold>\<box> cb'))) \<and>
          ((\<exists>ca'. cx = ca' \<^bold>\<box> cb) \<or> (\<exists>cb'. cx = ca \<^bold>\<box> cb'))\<close>)
       apply (elim conjE disjE[of \<open>\<exists>x y. sc' = _ x y\<close>] disjE[of \<open>\<exists>x. _ = _ x\<close>])
          apply (clarsimp, metis Endet.hyps(1) fst_conv)
         apply (clarsimp, blast)
        apply (clarsimp, blast)
       apply (clarsimp, metis Endet.hyps(2) fst_eqD)
      apply clarsimp
      apply (elim disjE; (simp; fail)?)
         apply (metis Endet.hyps(1) aopstep_then_aopstep_right_endetD fst_conv)
        apply fastforce
       apply fastforce
      apply (metis Endet.hyps(2) aopstep_then_aopstep_left_endetD fst_conv)
      done
  next
    case (Par \<pi>\<alpha> s ca cb sc')
    then show ?case
      apply (cases \<pi>\<alpha>, cases \<pi>\<alpha>x, rename_tac \<pi> \<alpha> \<pi>x \<alpha>x)
      apply clarsimp
      apply (case_tac \<open>\<pi> = PHere\<close>)
       apply (simp, metis aopstep.simps(1))
      apply (case_tac \<open>\<pi>x = PHere\<close>)
       apply (simp; fail)
      apply (case_tac \<open>
        (\<exists>\<pi>'. \<pi> = PL \<pi>') \<and> (\<exists>\<pi>'. \<pi>x = PL \<pi>') \<or>
        (\<exists>\<pi>'. \<pi> = PR \<pi>') \<and> (\<exists>\<pi>'. \<pi>x = PR \<pi>') \<or>
        (\<exists>\<pi>'. \<pi> = PL \<pi>') \<and> (\<exists>\<pi>'. \<pi>x = PR \<pi>') \<or>
        (\<exists>\<pi>'. \<pi> = PR \<pi>') \<and> (\<exists>\<pi>'. \<pi>x = PL \<pi>')\<close>)
       apply (elim conjE disjE[of \<open>Ex _ \<and> Ex _\<close>]; clarsimp; blast)
        (* other cases *)
      apply clarsimp
      apply metis
      done
  next
    case (DoLoop \<pi>\<alpha> s c sc')
    show ?case
      using DoLoop.prems
      apply clarsimp
      apply (metis DoLoop.hyps(1) aopstep_then_aopstep_right_seqD split_pairs2)
      done
  qed fastforce+
qed

lemmas btau_astep_preserves_nextstep2 =
  btau_astep_preserves_nextstep[of \<open>(\<pi>, \<alpha>)\<close> for \<pi> \<alpha>, simplified]

lemma btau_aexec_preserves_nextstep:
  \<open>sc \<midarrow>\<rho>\<rightarrow>\<^sub>a\<^sup>* sc' \<Longrightarrow>
    list_all ((=) TauBasic \<circ> snd) \<rho> \<Longrightarrow>
    list_all ((\<noteq>) \<pi>\<alpha>x) \<rho> \<Longrightarrow>
    sc \<midarrow>\<pi>\<alpha>x\<rightarrow>\<^sub>a scx \<Longrightarrow>
    \<exists>cx'. sc' \<midarrow>\<pi>\<alpha>x\<rightarrow>\<^sub>a (fst scx, cx')\<close>
  apply (induct arbitrary: \<pi>\<alpha>x scx rule: aopsteps_induct)
   apply force
  apply (simp, elim conjE)
  apply (frule(3) btau_astep_preserves_nextstep)
  apply (clarsimp, blast)
  done


lemma aopsteps_trans:
  \<open>sc \<midarrow>\<rho>a\<rightarrow>\<^sub>a\<^sup>* sc' \<Longrightarrow>
    sc' \<midarrow>\<rho>b\<rightarrow>\<^sub>a\<^sup>* sc'' \<Longrightarrow>
    sc \<midarrow>\<rho>a @ \<rho>b\<rightarrow>\<^sub>a\<^sup>* sc''\<close>
  by (induct arbitrary: \<rho>b sc'' rule: aopsteps.induct) force+

lemma basic_tau_aopstep_changes_comm:
  \<open>sc \<midarrow>\<pi>\<alpha>\<rightarrow>\<^sub>a sc' \<Longrightarrow>
    TauBasic = \<alpha> \<Longrightarrow>
    snd sc' \<noteq> snd sc\<close>
  by (induct rule: aopstep_induct) force+


subsection \<open> Basic-Tau Relations \<close>

(*
subsubsection \<open> Basic-Tau Reduction \<close>

definition btau_reduce_comm
  :: \<open>('l \<times> 's) \<Rightarrow> ('l \<times> 's) comm \<Rightarrow> ('l \<times> 's) comm \<Rightarrow> bool\<close> (\<open>_, _ \<leadsto>\<^sub>\<tau>\<^sub>B\<^sup>* _\<close> [55,0,55] 55)
  where
    \<open>s, c \<leadsto>\<^sub>\<tau>\<^sub>B\<^sup>* c' \<equiv> \<exists>\<rho>. list_all basic_tau_aact \<rho> \<and> (s, c) \<midarrow>\<rho>\<rightarrow>\<^sub>a\<^sup>* (s, c')\<close>

lemma btau_reduce_comm_reflI[intro]:
  \<open>btau_reduce_comm s c c\<close>
  by (metis aopsteps_nil btau_reduce_comm_def list_all_simps(2))

lemma btau_reduce_comm_reflp:
  \<open>reflp (btau_reduce_comm s)\<close>
  by (metis reflpI btau_reduce_comm_reflI)

lemma btau_reduce_comm_transp:
  \<open>transp (btau_reduce_comm s)\<close>
  by (rule transpI, meson aopsteps_trans btau_reduce_comm_def list_all_append)
*)

(* Note: \<open>btau_reduce_comm\<close> is not antisym, consider \<open>DO Skip;; Skip OD\<close> *)


subsubsection \<open> Basic-Tau Equiv \<close>

definition btau_equiv_trace :: \<open>aact eact list \<Rightarrow> aact eact list \<Rightarrow> bool\<close> (infix \<open>\<simeq>\<^sub>\<tau>\<^sub>B\<close> 55) where
  \<open>\<rho> \<simeq>\<^sub>\<tau>\<^sub>B \<rho>' \<equiv>
    List.filter (case_eact False ((\<noteq>) TauBasic)) \<rho> =
    List.filter (case_eact False ((\<noteq>) TauBasic)) \<rho>'\<close>

lemma nil_btau_equiv_iff[simp]:
  \<open>[] \<simeq>\<^sub>\<tau>\<^sub>B \<rho> \<longleftrightarrow> list_all (case_eact True ((=) TauBasic)) \<rho>\<close>
  by (induct \<rho>) (simp add: btau_equiv_trace_def split: eact.splits)+

lemma nil_btau_equiv_nil_iff[simp]:
  \<open>\<rho> \<simeq>\<^sub>\<tau>\<^sub>B [] \<longleftrightarrow> list_all (case_eact True ((=) TauBasic)) \<rho>\<close>
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
    List.filter (case_eact False ((\<noteq>) TauBasic)) \<rho> \<preceq>\<^sub>l
    List.filter (case_eact False ((\<noteq>) TauBasic)) \<rho>'\<close>

lemma nil_less_eq_btau_trace_iff[simp]:
  \<open>[] \<preceq>\<^sub>\<tau>\<^sub>B xs\<close>
  unfolding less_eq_btau_trace_def
  by force

subsection \<open> Head Enabled Equivalent States \<close>

definition
  \<open>head_enabled_equiv c sx sy \<equiv> \<forall>a\<in>#head_atoms c. pre_state a sx = pre_state a sy\<close>

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
  \<open>head_enabled_equiv \<langle>ar\<rangle> sx sy \<longleftrightarrow>
    pre_state ar sx = pre_state ar sy\<close>
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
  \<open>(s, c) \<midarrow>\<pi>\<alpha>\<rightarrow>\<^sub>a (ms', c') \<Longrightarrow>
    set_mset (do_loops c') \<subseteq> set_mset (do_loops c)\<close>
  by (induct c arbitrary: s ms' c' \<pi>\<alpha>)
    (fastforce simp add: if_bool_eq_disj conj_disj_distribL)+


subsection \<open> Do-Loop Enabled State Equivalence \<close>

abbreviation
  \<open>do_loop_head_enabled_equiv c sx sy \<equiv>
    \<forall>c'\<in>#do_loops c. head_enabled_equiv c' sx sy\<close>

lemma do_loop_head_enabled_equiv_iff[simp]:
  \<open>do_loop_head_enabled_equiv Skip sx sy\<close>
  \<open>do_loop_head_enabled_equiv \<langle>ar\<rangle> sx sy\<close>
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
    by (force simp add: if_bool_eq_disj pre_state_def)
qed (clarsimp simp add: all_conj_distrib; fail)+ (* slow *)


subsection \<open> Head Enabled Unique \<close>

definition
  \<open>head_enabled_unique c s \<equiv>
    \<forall>a\<in>#head_atoms c. \<forall>b\<in>#head_atoms c. pre_state a s = pre_state b s \<longrightarrow> a = b\<close>

subsubsection \<open> Do-guards Determinism \<close>

definition
  \<open>do_loops_determ c s \<equiv>
    (\<forall>c'\<in>#do_loops c.
      (\<forall>a. count (head_atoms c') a \<le> Suc 0) \<and>
      head_enabled_unique c' s)\<close>

lemma do_loops_determ_iff[simp]:
  \<open>do_loops_determ Skip s\<close>
  \<open>do_loops_determ \<langle>ar\<rangle> s\<close>
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
  \<open>(s, c) \<midarrow>\<pi>\<alpha>\<rightarrow>\<^sub>a (s', c') \<Longrightarrow>
    do_loop_head_enabled_equiv c s sa \<Longrightarrow>
    tau_aact (snd \<pi>\<alpha>) \<Longrightarrow>
    (sa, c) \<midarrow>\<pi>\<alpha>\<rightarrow>\<^sub>a (sa, c')\<close>
proof (induct c arbitrary: \<pi>\<alpha> s' c')
  case (Endet c1 c2)
  then show ?case by (simp, metis)
next
  case (Iter c)
  then show ?case by (simp, metis no_aopstep_head_enabled_equiv_state_irrel surj_pair)
qed fastforce+

(*
lemma aopsteps_tau_determ_doloop_then_state_irrel:
  \<open>(s, c) \<midarrow>\<rho>\<rightarrow>\<^sub>a\<^sup>* (s', c'') \<Longrightarrow>
    list_all tau_aact \<rho> \<Longrightarrow>
    do_loop_head_enabled_equiv c s sa \<Longrightarrow>
    (sa, c) \<midarrow>\<rho>\<rightarrow>\<^sub>a\<^sup>* (sa, c'')\<close>
  apply (induct \<rho> arbitrary: s c s' c'')
   apply force
  apply clarsimp
  apply (frule_tac sa=sa in aopstep_tau_determ_doloop_then_state_irrel, force, force)
  apply (frule aopstep_tau_preserves_state, blast)
  apply clarsimp
  apply (metis (no_types, lifting) aopstep_do_loops_subseteq subset_eq surj_pair)
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
  \<open>(s, c) \<midarrow>\<pi>\<alpha>\<rightarrow>\<^sub>a (s, cx') \<Longrightarrow>
    (s, c) \<midarrow>\<alpha>b\<rightarrow>\<^sub>a (s, cy') \<Longrightarrow>
    basic_tau_aact \<pi>\<alpha> \<Longrightarrow>
    basic_tau_aact \<alpha>b \<Longrightarrow>
    cx' \<noteq> cy' \<Longrightarrow>
    (\<exists>c'. (s, cy') \<midarrow>\<pi>\<alpha>\<rightarrow>\<^sub>a (s, c')) \<or>
    (\<exists>c'. (s, cx') \<midarrow>\<alpha>b\<rightarrow>\<^sub>a (s, c'))\<close>
  apply (induct c arbitrary: s \<pi>\<alpha> \<alpha>b cx' cy')
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
  (\<exists>\<pi>\<alpha>a. \<pi>\<alpha> = PL \<pi>\<alpha>a) \<and> (\<exists>\<pi>\<alpha>b. \<alpha>b = PL \<pi>\<alpha>b) \<or>
  (\<exists>\<pi>\<alpha>a. \<pi>\<alpha> = PR \<pi>\<alpha>a) \<and> (\<exists>\<pi>\<alpha>b. \<alpha>b = PR \<pi>\<alpha>b)\<close>)
    (** the difficult cases **)
       apply (elim disjE[of \<open>_ \<and> Ex _\<close>])
        apply (clarsimp, blast)
       apply (clarsimp, blast)
    (** the rest **)
      apply (elim disjE; force)
    (* Indet *)
     apply force
    (* Endet *)
    apply (clarsimp del: disjCI)
    apply (case_tac \<open>
  (\<exists>ca. cx' = ca \<^bold>\<box> c2) \<and> (\<exists>ca. cy' = ca \<^bold>\<box> c2) \<or>
  (\<exists>cb. cx' = c1 \<^bold>\<box> cb) \<and> (\<exists>cb. cy' = c1 \<^bold>\<box> cb) \<or>
  (\<exists>cb. cx' = c1 \<^bold>\<box> cb) \<and> (\<exists>ca. cy' = ca \<^bold>\<box> c2) \<or>
  (\<exists>ca. cx' = ca \<^bold>\<box> c2) \<and> (\<exists>cb. cy' = c1 \<^bold>\<box> cb)\<close>)
      (** the difficult cases **)
     apply (elim disjE[of \<open>Ex _ \<and> Ex _\<close>])
        apply (clarsimp, metis basic_tau_aact_then_tau_aact vis_tau_aact_incompatible(1))
       apply (clarsimp, metis basic_tau_aact_then_tau_aact vis_tau_aact_incompatible(1))
      apply force
     apply force
    (** the easy cases **)
    apply (elim disjE; simp add: vis_tau_aact_incompatible(2); blast)
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
          ((s, c), (s, c))
            =R, F, (map Loc \<rho>x, \<rho>y)\<Rightarrow>\<^sub>\<E>\<^sup>*
            ((s, cx), (s, cy))))\<close>
  apply (induct arbitrary: s c cx rule: aopsteps_rev.induct)
   apply force
  apply clarsimp
  apply (subst dexec_exact_left_rcons_iff)
  apply clarsimp
  oops


definition
  \<open>invt_exec_prop p sc \<equiv> \<forall>\<rho> sc'. sc \<midarrow>\<rho>\<rightarrow>\<^sub>a\<^sup>* sc' \<longrightarrow> p sc'\<close>

lemma invt_exec_prop_iff:
  \<open>invt_exec_prop p (s, Skip) \<longleftrightarrow> p (s, Skip)\<close>
  \<open>invt_exec_prop p (s, ca ;; cb) \<longleftrightarrow>
    p (s, ca ;; cb) \<and>
    (ca = Skip \<longrightarrow> invt_exec_prop p (s, cb)) \<and>
    (\<forall>s' ca'. (\<exists>\<alpha>. (s, ca) \<midarrow>\<pi>\<alpha>\<rightarrow>\<^sub>a (s', ca')) \<longrightarrow> invt_exec_prop p (s', ca' ;; cb))\<close>
  \<open>invt_exec_prop p (s, ca \<^bold>\<sqinter> cb) \<longleftrightarrow>
    p (s, ca \<^bold>\<sqinter> cb) \<and>
    invt_exec_prop p (s, ca) \<and>
    invt_exec_prop p (s, cb)\<close>
  \<open>invt_exec_prop p (s, ca \<^bold>\<box> cb) \<longleftrightarrow>
    p (s, ca \<^bold>\<box> cb) \<and>
    (ca = Skip \<longrightarrow> invt_exec_prop p (s, cb)) \<and>
    (cb = Skip \<longrightarrow> invt_exec_prop p (s, ca)) \<and>
    (\<forall>\<alpha>. tau_aact \<alpha> \<longrightarrow>
      (\<forall>ca' s'. (s, ca) \<midarrow>\<pi>\<alpha>\<rightarrow>\<^sub>a (s', ca') \<longrightarrow> invt_exec_prop p (s', ca' \<^bold>\<box> cb)) \<and>
      (\<forall>cb' s'. (s, cb) \<midarrow>\<pi>\<alpha>\<rightarrow>\<^sub>a (s', cb') \<longrightarrow> invt_exec_prop p (s', ca \<^bold>\<box> cb'))) \<and>
    (\<forall>\<alpha>. vis_aact \<alpha> \<longrightarrow>
      (\<forall>s' ca'. (s, ca) \<midarrow>\<pi>\<alpha>\<rightarrow>\<^sub>a (s', ca') \<longrightarrow> invt_exec_prop p (s', ca')) \<and>
      (\<forall>s' cb'. (s, cb) \<midarrow>\<pi>\<alpha>\<rightarrow>\<^sub>a (s', cb') \<longrightarrow> invt_exec_prop p (s', cb')))\<close>
  \<open>invt_exec_prop p (s, ca \<parallel> cb) \<longleftrightarrow>
    p (s, ca \<parallel> cb) \<and>
    (ca = Skip \<longrightarrow> cb = Skip \<longrightarrow> p (s, Skip)) \<and>
    (\<forall>\<alpha> s' ca'. (s, ca) \<midarrow>\<pi>\<alpha>\<rightarrow>\<^sub>a (s', ca') \<longrightarrow> invt_exec_prop p (s', ca' \<parallel> cb)) \<and>
    (\<forall>\<alpha> s' cb'. (s, cb) \<midarrow>\<pi>\<alpha>\<rightarrow>\<^sub>a (s', cb') \<longrightarrow> invt_exec_prop p (s', ca \<parallel> cb'))\<close>
  \<open>invt_exec_prop p (s, \<langle>ar\<rangle>) \<longleftrightarrow>
    (p (s, \<langle>ar\<rangle>) \<and>
    (\<forall>s'. ar s s' \<longrightarrow> p (s', Skip)))\<close>
  \<open>invt_exec_prop p (s, DO c OD) \<longleftrightarrow>
    (p (s, DO c OD) \<and>
    ((\<forall>\<alpha> s' c'. \<not> (s, c) \<midarrow>\<pi>\<alpha>\<rightarrow>\<^sub>a (s', c')) \<longrightarrow> p (s, Skip)) \<and>
    (\<forall>\<alpha> s' c'. (s, c) \<midarrow>\<pi>\<alpha>\<rightarrow>\<^sub>a (s', c') \<longrightarrow> invt_exec_prop p (s', c' ;; DO c OD)))\<close>
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
    (* Parallel *)
    apply (simp add: invt_exec_prop_def)
    apply (subst aopsteps_iff)
    apply (clarsimp simp add: all_conj_distrib imp_ex_conjL imp_conjL imp_conjR ex_disj_distrib
      conj_disj_distribR split_pairs split_pairs2)
    apply blast
    (* Atom *)
   apply (simp add: invt_exec_prop_def)
   apply (subst aopsteps_iff)
   apply (clarsimp simp add: all_conj_distrib imp_ex_conjL split_pairs split_pairs2)
    (* Do-loop *)
  apply (simp add: invt_exec_prop_def)
  apply (subst aopsteps_iff)
  apply (clarsimp simp add: all_conj_distrib imp_ex_conjL split_pairs split_pairs2)
  apply blast
  done


definition
  \<open>comm_determ sc \<equiv> \<forall>\<rho> sc'. sc \<midarrow>\<rho>\<rightarrow>\<^sub>a\<^sup>* sc' \<longrightarrow> (\<forall>sc''. sc \<midarrow>\<rho>\<rightarrow>\<^sub>a\<^sup>* sc'' \<longrightarrow> snd sc' = snd sc'')\<close>

definition
  \<open>hatoms_determ sc \<equiv>
    \<forall>arx\<in>#head_atoms (snd sc). \<forall>ary\<in>#head_atoms (snd sc).
      pre_state arx (fst sc) = pre_state ary (fst sc)\<close>

lemmas hatoms_determ_fold = hatoms_determ_def[symmetric, of \<open>(s,c)\<close> for s c, simplified]

abbreviation \<open>invt_hatoms_determ \<equiv> invt_exec_prop hatoms_determ\<close>


lemma vis_aopstep_hatoms_determ_implies_comm_determ':
  \<open>sc \<midarrow>\<pi>\<alpha>\<rightarrow>\<^sub>a scx' \<Longrightarrow>
    sc \<midarrow>\<pi>\<alpha>\<rightarrow>\<^sub>a scy' \<Longrightarrow>
    vis_aact \<alpha> \<Longrightarrow>
    hatoms_determ sc \<Longrightarrow>
    snd scx' = snd scy'\<close>
  apply (induct \<alpha> sc scx' arbitrary: scy' rule: aopstep_induct)
        apply force
       apply clarsimp
       apply (elim disjE)
          apply force
         apply force
        apply force
       apply clarsimp
       apply (subst (asm)(2) hatoms_determ_def)
       apply (simp add: hatoms_determ_fold; fail)
      apply force
  subgoal sorry
  subgoal sorry
  subgoal sorry
  apply force
  oops

lemma aopstep_preserves_hatoms_determ:
  \<open>sc \<midarrow>\<pi>\<alpha>\<rightarrow>\<^sub>a sc' \<Longrightarrow>
    sc' = (s', c') \<Longrightarrow>
    hatoms_determ sc \<Longrightarrow>
    hatoms_determ (s', c')\<close>
  apply (induct arbitrary: s' c' rule: aopstep_induct)
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
  oops

lemma
  \<open>hatoms_determ sc \<Longrightarrow> comm_determ sc\<close>
  apply (clarsimp simp add: hatoms_determ_def comm_determ_def)
  oops
*)

(*
lemma dstep_conf_to_dexec_exact:
  assumes
    \<open>((sx, cx), (sy, cy))
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
      ((sx, c), (sy, c))
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
    \<open>((fst sx' + fx, snd sx'), cx) \<midarrow>\<pi>\<alpha>\<rightarrow>\<^sub>a (Inr (), cx')\<close>
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
    \<open>((fst sy' + fy, snd sy'), cy) \<midarrow>\<pi>\<alpha>\<rightarrow>\<^sub>a (Inr (), cy')\<close>
  then show ?thesis
    sorry
next
  fix fx sx \<alpha> cy cx
  presume
    \<open>\<rho>x = [Loc \<alpha>]\<close>
    \<open>\<rho>y = []\<close>
    \<open>ss = ((sx, cx), (sy', ky'), cy)\<close>
    \<open>\<not> kx'\<close>
    \<open>\<exists>fy. F ((fx, fy), snd sx, snd sy') \<and> fst sy' ## fy\<close>
    \<open>nonsync_aact \<alpha>\<close>
    \<open>fst sx ## fx\<close>
    \<open>((fst sx + fx, snd sx), cx) \<midarrow>\<pi>\<alpha>\<rightarrow>\<^sub>a ((fst sx' + fx, snd sx'), cx')\<close>
  then show ?thesis
    sorry
next
  fix fy sy \<alpha> cy
  presume
    \<open>\<rho>x = []\<close>
    \<open>\<rho>y = [Loc \<alpha>]\<close>
    \<open>ss = (((sx', kx'), cx'), sy, cy)\<close>
    \<open>\<not> ky'\<close>
    \<open>\<exists>fx. F ((fx, fy), snd sx', snd sy) \<and> fst sx' ## fx\<close>
    \<open>nonsync_aact \<alpha>\<close>
    \<open>fst sy ## fy\<close>
    \<open>((fst sy + fy, snd sy), cy) \<midarrow>\<pi>\<alpha>\<rightarrow>\<^sub>a ((fst sy' + fy, snd sy'), cy')\<close>
  show ?thesis
    sorry
next
  fix fx fy sx sy \<alpha> cx cy 
  presume
    \<open>\<rho>x = [Loc \<alpha>]\<close>
    \<open>\<rho>y = [Loc \<alpha>]\<close>
    \<open>ss = ((sx, cx), sy, cy)\<close>
    \<open>\<not> kx'\<close>
    \<open>\<not> ky'\<close>
    \<open>F ((fx, fy), snd sx, snd sy)\<close>
    \<open>\<not> nonsync_aact \<alpha>\<close>
    \<open>fst sx ## fx\<close>
    \<open>((fst sx + fx, snd sx), cx) \<midarrow>\<pi>\<alpha>\<rightarrow>\<^sub>a ((fst sx' + fx, snd sx'), cx')\<close>
    \<open>fst sx ## fx\<close>
    \<open>((fst sy + fy, snd sy), cy) \<midarrow>\<pi>\<alpha>\<rightarrow>\<^sub>a ((fst sy' + fy, snd sy'), cy')\<close>
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
    ss = ((sx, c), sy, c) \<Longrightarrow>
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
    ss = ((sx, c), sy, c) \<Longrightarrow>
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
    ss = ((sx, c), sy, c) \<Longrightarrow>
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

lemma dexec_conf_to_eaopsteps:
  \<open>ss =R, F, \<rho>\<rho>\<Rightarrow>\<^sub>\<C>\<^sup>* ss' \<Longrightarrow>
    ss = ((sx, c), (sy, c)) \<Longrightarrow>
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
*)


section \<open> Jul-Aug Attempt \<close>


definition
  \<open>must_sync \<pi>\<alpha> \<equiv>
    fst \<pi>\<alpha> \<noteq> PHere \<or>
    snd \<pi>\<alpha> = TauINdetL \<or>
    snd \<pi>\<alpha> = TauINdetR\<close>


inductive dopstep
  :: \<open>(plabel \<times> aact) list \<times> (plabel \<times> aact) list \<Rightarrow>
      (('l::pre_perm_alg \<times> 's) \<times> ('l \<times> 's) comm) \<times> (('l \<times> 's) \<times> ('l \<times> 's) comm) \<Rightarrow>
      (('l \<times> 's) \<times> ('l \<times> 's) comm) \<times> (('l \<times> 's) \<times> ('l \<times> 's) comm) \<Rightarrow>
      bool\<close>
  where
    dopstep_step_left[intro!]:
  \<open>\<not> must_sync \<pi>\<alpha> \<Longrightarrow>
    \<comment> \<open> left step \<close>
    (sx, cx) \<midarrow>\<pi>\<alpha>\<rightarrow>\<^sub>a (sx', cx') \<Longrightarrow>
    dopstep ([\<pi>\<alpha>], []) ((sx, cx), (sy, cy)) ((sx', cx'), (sy, cy))\<close>
| dopstep_step_right[intro!]:
  \<open>\<not> must_sync \<pi>\<alpha> \<Longrightarrow>
    \<comment> \<open> right step \<close>
    (sy, cy) \<midarrow>\<pi>\<alpha>\<rightarrow>\<^sub>a (sy', cy') \<Longrightarrow>
    dopstep ([], [\<pi>\<alpha>]) ((sx, cx), (sy, cy)) ((sx, cx), (sy', cy'))\<close>
| dopstep_local[intro]:
  \<open>\<comment> \<open> left step \<close>
    (sx, cx) \<midarrow>\<pi>\<alpha>\<rightarrow>\<^sub>a (sx', cx') \<Longrightarrow>
    \<comment> \<open> right step \<close>
    (sy, cy) \<midarrow>\<pi>\<alpha>\<rightarrow>\<^sub>a (sy', cy') \<Longrightarrow>
    dopstep ([\<pi>\<alpha>], [\<pi>\<alpha>]) ((sx, cx), (sy, cy)) ((sx', cx'), (sy', cy'))\<close>

inductive_cases dopstep_nil_leftE[elim!]: \<open>dopstep ([], \<rho>y) scxy scxy'\<close>
inductive_cases dopstep_nil_rightE[elim!]: \<open>dopstep (\<rho>x, []) scxy scxy'\<close>
inductive_cases dopstep_sync_moveE[elim!]: \<open>dopstep ([\<pi>\<alpha>x], [\<pi>\<alpha>y]) scxy scxy'\<close>

abbreviation dopstep_pretty :: \<open>_ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> bool\<close>
  (\<open>_ =_\<Rightarrow> _\<close> [50, 0, 50])
  where
    \<open>ss =\<rho>xy\<Rightarrow> ss' \<equiv> dopstep \<rho>xy ss ss'\<close>

lemma dopstep_simps[simp]:
  \<open>dopstep (\<rho>x, []) scxy scxy' \<longleftrightarrow>
    (\<exists>\<pi>\<alpha> scx scx' scy.
      \<rho>x = [\<pi>\<alpha>] \<and>
      scxy = (scx, scy) \<and>
      scxy' = (scx', scy) \<and>
      must_sync \<pi>\<alpha> \<and>
      scx \<midarrow>\<pi>\<alpha>\<rightarrow>\<^sub>a scx')\<close>
  \<open>dopstep ([], \<rho>y) scxy scxy' \<longleftrightarrow>
    (\<exists>\<pi>\<alpha> scy scy' scx.
      \<rho>y = [\<pi>\<alpha>] \<and>
      scxy = (scx, scy) \<and>
      scxy' = (scx, scy') \<and>
      must_sync \<pi>\<alpha> \<and>
      scy \<midarrow>\<pi>\<alpha>\<rightarrow>\<^sub>a scy')\<close>
  \<open>dopstep ([\<pi>\<alpha>x], [\<pi>\<alpha>y]) scxy scxy' \<longleftrightarrow>
    \<pi>\<alpha>y = \<pi>\<alpha>x \<and>
    (\<exists>scx scx' scy scy'.
        scxy = (scx, scy) \<and>
        scxy' = (scx', scy') \<and>
        scx \<midarrow>\<pi>\<alpha>x\<rightarrow>\<^sub>a scx' \<and>
        scy \<midarrow>\<pi>\<alpha>x\<rightarrow>\<^sub>a scy')\<close>
  by force+


text \<open>
  TODO: describe
\<close>
inductive secure
  :: \<open>('s \<times> 's \<Rightarrow> 's \<times> 's \<Rightarrow> bool) \<Rightarrow>
      (('l, 's) rgstate \<Rightarrow> bool) \<Rightarrow>
      ('s \<times> 's \<Rightarrow> 's \<times> 's \<Rightarrow> bool) \<Rightarrow>
      (('l, 's) rgstate \<Rightarrow> bool) \<Rightarrow>
      (('l, 's) rgstate \<Rightarrow> bool) \<Rightarrow>
      nat \<Rightarrow>
      ('l::pre_perm_alg \<times> 's) comm \<times> ('l::pre_perm_alg \<times> 's) comm \<Rightarrow>
      ('l, 's) secstate \<Rightarrow>
      bool\<close>
  for R F G I q
  where
  secure_nil[intro!]: \<open>secure R F G I q 0 cc zz\<close>
| secure_suc[intro]:
  \<open>cc = (cx, cy) \<Longrightarrow>
    zz = ((slx::'l, ssx::'s), (sly::'l, ssy::'s)) \<Longrightarrow>
    \<comment> \<open> Post-condition
         Note that both programs need to be terminated. \<close>
    cx = Skip \<longrightarrow> cy = Skip \<longrightarrow> q ((slx, sly), (ssx, ssy)) \<Longrightarrow>
    \<comment> \<open> State Invariant \<close>
    I ((slx, sly), (ssx, ssy)) \<Longrightarrow>
    \<comment> \<open> Rely Steps \<close>
    (\<And>ssx' ssy'.
      R (ssx, ssy) (ssx', ssy') \<Longrightarrow>
      secure R F G I q n cc ((slx, ssx'), (sly, ssy'))) \<Longrightarrow>
    \<comment> \<open> Opsteps \<close>
    (\<And>fx fy \<rho>x \<rho>y slfx' slfy' ssx' ssy' cx' cy'.
        F ((fx, fy), (ssx, ssy)) \<Longrightarrow>
        slx ## fx \<Longrightarrow>
        sly ## fy \<Longrightarrow>
        ( ((slx + fx, ssx), cx), ((sly + fy, ssy), cy) )
          =(\<rho>x, \<rho>y)\<Rightarrow> ( ((slfx', ssx'), cx'), ((slfy', ssy'), cy') ) \<Longrightarrow>
        \<comment> \<open> Non-tau steps establish the guarantee.
              We want the guarantee to be established when a vis move happens
              in \<^emph>\<open>either\<close> run. But this leaves the question of what we shold do
              with the other run. Requiring both perform a simultaneous vis step
              is too restrictive.
                Here, we say that if either performs a vis, we must establish
              the guarantee. But note! Due to the way double-opstep is defined,
              when there is a one-sided step, the other side stutters. Thus
              if you want to property generalise your guarantees from single state,
              and you \<^emph>\<open>don't\<close> know every move will be synchronised, you should lift
              the guarantee as follows: \<open>Ga\<^sup>=\<^sup>= \<times>\<^sub>R Gb \<squnion> Ga \<times>\<^sub>R Gb\<^sup>=\<^sup>=\<close>.
            \<close>
        (\<forall>\<pi>\<alpha>. \<rho>x = [\<pi>\<alpha>] \<longrightarrow> vis_aact (snd \<pi>\<alpha>) \<longrightarrow> G (ssx, ssy) (ssx', ssy')) \<and>
        (\<forall>\<pi>\<alpha>. \<rho>y = [\<pi>\<alpha>] \<longrightarrow> vis_aact (snd \<pi>\<alpha>) \<longrightarrow> G (ssx, ssy) (ssx', ssy')) \<and>
        (\<exists>slx'.
          slx' ## fx \<and>
          slfx' = slx' + fx \<and>
          (\<forall>\<pi>\<alpha>x. \<rho>x = [\<pi>\<alpha>x] \<longrightarrow> tau_aact (snd \<pi>\<alpha>x) \<longrightarrow> slx' = slx) \<and>
          (\<exists>sly'.
            sly' ## fy \<and>
            slfy' = sly' + fy \<and>
            (\<forall>\<pi>\<alpha>y. \<rho>y = [\<pi>\<alpha>y] \<longrightarrow> tau_aact (snd \<pi>\<alpha>y) \<longrightarrow> sly' = sly) \<and>
            secure R F G I q n (cx', cy') ((slx', ssx'), (sly', ssy')) ))) \<Longrightarrow>
    \<comment> \<open> conclude a step can be made \<close>
    secure R F G I q (Suc n) cc zz\<close>


lemma head_atomic_implies_all_steps_vis:
  \<open>sc \<midarrow>\<pi>\<alpha>\<rightarrow>\<^sub>a sc' \<Longrightarrow>
    head_atomic (snd sc) \<Longrightarrow>
    vis_aact (snd \<pi>\<alpha>)\<close>
  by (induct _ sc sc' rule: aopstep_induct) auto


fun sec_determ :: \<open>('l \<times> 's) comm \<Rightarrow> ('l, 's) secstate \<Rightarrow> bool\<close> where
  \<open>sec_determ (ca \<^bold>\<box> cb) = (\<lambda>(sx, sy).
    head_atomic ca \<and> head_atomic cb \<and>
    (\<forall>ra \<in># head_atoms ca.
      \<forall>rb \<in># head_atoms cb.
        \<not> (pre_state ra sx \<and> pre_state rb sy) \<and>
        \<not> (pre_state rb sx \<and> pre_state ra sy))
  )\<close>
| \<open>sec_determ (DO c OD) = (\<lambda>(sx, sy).
    head_atomic c \<and>
    pre_state (\<Squnion>(set_mset (head_atoms c))) sx =
      pre_state (\<Squnion>(set_mset (head_atoms c))) sy)\<close>
| \<open>sec_determ c = (\<lambda>_. True)\<close>

lemma sec_determ_symp:
  \<open>symp (curry (sec_determ c))\<close>
  by (induct c) (force simp add: symp_def)+

lemma sec_determ_quasireflp:
  \<open>quasireflp (curry (sec_determ c))\<close>
  apply (induct c)
        apply (simp add: prepost_state_def' reflp_on_def)+
    apply clarsimp
    apply (case_tac \<open>\<not> head_atomic c1\<close>, blast)
    apply (case_tac \<open>\<not> head_atomic c2\<close>, blast)
    apply clarsimp
  oops

definition
  \<open>all_sec_determ c \<equiv> \<Sqinter>{sec_determ c'|c'. c' \<le> c}\<close>

lemma all_sec_determ_eq[simp]:
  \<open>all_sec_determ Skip = \<top>\<close>
  \<open>all_sec_determ (ca ;; cb) = all_sec_determ ca \<sqinter> all_sec_determ cb\<close>
  \<open>all_sec_determ (ca \<^bold>\<sqinter> cb) = all_sec_determ ca \<sqinter> all_sec_determ cb\<close>
  \<open>all_sec_determ \<langle>ra\<rangle> = \<top>\<close>
  \<open>all_sec_determ (ca \<parallel> cb) = all_sec_determ ca \<sqinter> all_sec_determ cb\<close>
  \<open>all_sec_determ (ca \<^bold>\<box> cb) =
    (\<lambda>_. head_atomic ca) \<sqinter>
    (\<lambda>_. head_atomic cb) \<sqinter>
    (\<lambda>(sx, sy).
      \<forall>ra\<in>#head_atoms ca.
         \<forall>rb\<in>#head_atoms cb.
            (pre_state ra sx \<longrightarrow> \<not> pre_state rb sy) \<and>
            (pre_state rb sx \<longrightarrow> \<not> pre_state ra sy)) \<sqinter>
    all_sec_determ ca \<sqinter>
    all_sec_determ cb\<close>
  \<open>all_sec_determ (DO c OD) =
    (\<lambda>_. head_atomic c) \<sqinter>
    (\<lambda>(sx, sy).
      pre_state (\<Squnion> set_mset (head_atoms c)) sx =
      pre_state (\<Squnion> set_mset (head_atoms c)) sy) \<sqinter>
    all_sec_determ c\<close>
  by (clarsimp simp add: all_sec_determ_def conj_disj_distribL
      ex_disj_distrib Collect_disj_eq; blast)+

lemma all_sec_determ_implies_sec_determ:
  \<open>all_sec_determ c s \<Longrightarrow> sec_determ c s\<close>
  by (clarsimp simp add: all_sec_determ_def, blast)


subsubsection \<open> The Key Lemmas \<close>


lemma state_in_head_guards_then_aopstep_exists:
  \<open>pre_state (\<Squnion> set_mset (head_atoms c)) s \<Longrightarrow>
    \<exists>\<pi>\<alpha> sc'. (s, c) \<midarrow>\<pi>\<alpha>\<rightarrow>\<^sub>a sc' \<and> vis_aact (snd \<pi>\<alpha>)\<close>
proof (induct c)
  case (Seq c1 c2)
  then show ?case
    by (clarsimp simp add: pre_state_def, metis)
next
  case (Par c1 c2)
  then show ?case
    by (clarsimp simp add: pre_state_def, metis)
next
  case (Endet c1 c2)
  then show ?case
    by (clarsimp simp add: pre_state_def, metis)
qed (clarsimp simp add: pre_state_def; blast)+

lemma state_not_in_head_guards_then_no_aopstep:
  \<open>head_atomic c \<Longrightarrow>
    \<not> pre_state (\<Squnion> set_mset (head_atoms c)) s \<Longrightarrow>
    (s, c) \<midarrow>/\<rightarrow>\<^sub>a \<close>
proof (induct c)
  case (Seq c1 c2)
  then show ?case
    by (metis aopstep.simps(2) head_atomic.simps(1-2) head_atoms.simps(2))
next
  case (Par c1 c2)
  then show ?case
    by (simp add: pre_state_def ball_Un, metis head_atomic.simps(1))
next
  case (Endet c1 c2)
  then show ?case
    by (simp add: pre_state_def ball_Un, metis head_atomic.simps(1))
next
  case (Iter c)
  then show ?case
    by (metis head_atomic.simps(7))
qed (simp add: pre_state_def)+

lemma state_not_in_head_guards_iff_not_nostep:
  \<open>head_atomic c \<Longrightarrow>
    pre_state (\<Squnion> set_mset (head_atoms c)) s \<longleftrightarrow>
      \<not> ((s, c) \<midarrow>/\<rightarrow>\<^sub>a)\<close>
  by (metis state_in_head_guards_then_aopstep_exists
      state_not_in_head_guards_then_no_aopstep)

lemma head_atomic_nostep_iff_state_not_in_head_guards:
  \<open>head_atomic c \<Longrightarrow>
    (s, c) \<midarrow>/\<rightarrow>\<^sub>a \<longleftrightarrow>
      \<not> pre_state (\<Squnion> set_mset (head_atoms c)) s\<close>
  using state_not_in_head_guards_iff_not_nostep
  by metis

lemma head_atomic_opstep_vis_aact:
  \<open>sc \<midarrow>\<pi>\<alpha>\<rightarrow>\<^sub>a sc' \<Longrightarrow>
    head_atomic (snd sc) \<Longrightarrow>
    vis_aact (snd \<pi>\<alpha>)\<close>
  by (induct _ sc sc' rule: aopstep_induct) fastforce+



text \<open>
  Note with this theorem that we still permits can be atomic non-determinism.
  So when starting with the same state, it is not necessarily the case
  that the result state is the same.
\<close>
lemma sec_determ_implies_step_determ_up_to_scheduling:
  assumes
    \<open>all_sec_determ c (sx, sy)\<close>
    \<open>(sx, c) \<midarrow>\<pi>\<alpha>x\<rightarrow>\<^sub>a (sx', cx')\<close>
    \<open>(sy, c) \<midarrow>\<pi>\<alpha>y\<rightarrow>\<^sub>a (sy', cy')\<close>
    \<open>fst \<pi>\<alpha>x = fst \<pi>\<alpha>y\<close> \<comment> \<open> same schedule \<close>
    \<open>snd \<pi>\<alpha>x \<noteq> TauINdetL\<close>
    \<open>snd \<pi>\<alpha>x \<noteq> TauINdetR\<close>
    \<open>snd \<pi>\<alpha>y \<noteq> TauINdetL\<close>
    \<open>snd \<pi>\<alpha>y \<noteq> TauINdetR\<close>
  shows
    \<open>snd \<pi>\<alpha>x = snd \<pi>\<alpha>y \<and> cx' = cy'\<close>
  using assms
proof (induct c arbitrary: sx sy \<pi>\<alpha>x \<pi>\<alpha>y sx' cx' sy' cy')
  case (Seq ca cb)
  show ?case
    using Seq.prems Seq.hyps(1)[of _ _ \<pi>\<alpha>x _ _ \<pi>\<alpha>y]
    by (simp, metis aopstep.simps(1))
next
  case (Par c1 c2)
  show ?case
    using Par.prems
    apply simp
    apply (case_tac \<open>
      (\<exists>\<pi>x' \<alpha>'. \<pi>\<alpha>x = (PL \<pi>x', \<alpha>')) \<and> (\<exists>\<pi>y' \<alpha>'. \<pi>\<alpha>y = (PL \<pi>y', \<alpha>')) \<or>
      (\<exists>\<pi>x' \<alpha>'. \<pi>\<alpha>x = (PR \<pi>x', \<alpha>')) \<and> (\<exists>\<pi>y' \<alpha>'. \<pi>\<alpha>y = (PR \<pi>y', \<alpha>'))\<close>)
     apply (elim disjE[of \<open>Ex _ \<and> Ex _\<close>] conjE exE; simp; elim disjE conjE exE)
      apply (metis Par.hyps(1) fst_conv snd_conv)
     apply (metis Par.hyps(2) fst_conv snd_conv)
    apply (elim disjE conjE exE; simp; fail)
    done
next
  case (Indet c1 c2)
  then show ?case by auto
next
  case (Endet c1 c2)
  show ?case
    using Endet.prems
    apply clarsimp
    apply (case_tac \<open>c1 = Skip\<close>, force)
    apply (case_tac \<open>c2 = Skip\<close>, force)
    apply (case_tac \<open>
      (\<exists>c'. cx' = c1 \<^bold>\<box> c') \<and> (\<exists>c'. cy' = c1 \<^bold>\<box> c') \<or>
      (\<exists>c'. cx' = c' \<^bold>\<box> c2) \<and> (\<exists>c'. cy' = c' \<^bold>\<box> c2) \<or>
      (\<exists>c'. cx' = c' \<^bold>\<box> c2) \<and> (\<exists>c'. cy' = c1 \<^bold>\<box> c') \<or>
      (\<exists>c'. cx' = c1 \<^bold>\<box> c') \<and> (\<exists>c'. cy' = c' \<^bold>\<box> c2) \<close>)
     apply (elim disjE[of \<open>Ex _ \<and> Ex _\<close>])
        apply clarsimp
        apply (metis Endet.hyps(2)[of _ _ \<pi>\<alpha>x _ _ \<pi>\<alpha>y] comm.inject(4) not_tau_aact_iff)
       apply clarsimp
       apply (metis Endet.hyps(1)[of _ _ \<pi>\<alpha>x _ _ \<pi>\<alpha>y] comm.inject(4) not_tau_aact_iff)
      apply clarsimp
    sorry
next
  case (Iter c)
  show ?case
    using Iter.prems
    by (simp del: split_paired_All
        add: head_atomic_nostep_iff_state_not_in_head_guards,
        metis Iter.hyps state_not_in_head_guards_then_no_aopstep)
qed simp+


lemma all_sec_determ_not_must_sync_then_only_one_action:
  assumes
    \<open>sc \<midarrow>\<pi>\<alpha>\<rightarrow>\<^sub>a sc'\<close>
    \<open>\<not> must_sync \<pi>\<alpha>\<close>
    \<open>all_sec_determ (snd sc) (fst sc, sy)\<close>
    \<open>(sy, snd sc) \<midarrow>\<pi>\<alpha>y\<rightarrow>\<^sub>a (sy', cy')\<close>
  shows
    \<open>\<pi>\<alpha>y = \<pi>\<alpha> \<and> cy' = snd sc'\<close>
  using assms
  apply (induct _ sc sc' arbitrary: sy sy' cy' \<pi>\<alpha>y rule: aopstep_induct)
        apply force
       apply force
      apply (force simp add: must_sync_def)
     apply (simp add: must_sync_def)
     apply (case_tac \<open>vis_aact (snd \<pi>\<alpha>)\<close>)
      apply (metis fst_conv head_atomic.simps(1) head_atomic_opstep_vis_aact
      not_tau_aact_iff pre_state_def snd_conv vis_aopstep_impl_atom)
     apply simp
     apply (metis head_atomic.simps(1) head_atomic_opstep_vis_aact prod_eq_decompose(1)
      tau_aact_def vis_aact_not_TauBasic(3))
    apply (force simp add: must_sync_def)
   apply (simp add: must_sync_def)
   apply (elim conjE exE)
   apply (simp add: vis_tau_aact_incompatible state_not_in_head_guards_iff_not_nostep
      del: split_paired_All split_paired_Ex)
   apply (clarsimp, blast)
  apply force
  done

lemma all_sec_determ_implies_paired_step_right:
  assumes
    \<open>sc \<midarrow>\<pi>\<alpha>\<rightarrow>\<^sub>a sc'\<close>
    \<open>all_sec_determ (snd sc) (fst sc, sy)\<close>
  shows
    \<open>\<exists>sy'. (sy, snd sc) \<midarrow>\<pi>\<alpha>\<rightarrow>\<^sub>a (sy', snd sc')\<close>
  using assms
  \<comment> \<open> not true, as we might get stuck. If we assume we don't, it's just the previous theorem. \<close>
  oops

lemma aopstep_equiv_guard_head_state_irrelevant:
  assumes
    \<open>sc \<midarrow>\<alpha>\<rightarrow>\<^sub>a sc'\<close>
    \<open>all_sec_determ (snd sc) (fst sc, sx)\<close>
    \<open>(\<Squnion>(set_mset (head_atoms (snd sc)))) (fst sc) =
      (\<Squnion>(set_mset (head_atoms (snd sc)))) sx\<close>
  shows
    \<open>\<exists>sx'. (sx, snd sc) \<midarrow>\<alpha>\<rightarrow>\<^sub>a (sx', snd sc')\<close>
  using assms
proof (induct _ sc sc' rule: aopstep_induct)
  case (Seq \<pi>\<alpha> s ca cb sc')
  then show ?case
    by (simp add: fun_eq_iff, metis split_pairs)
next
  case (Endet \<pi>\<alpha> s ca cb sc')
  then show ?case
    apply (clarsimp simp add: fun_eq_iff)
    apply (elim disjE conjE exE)
         apply (simp; fail)
        apply (simp; fail)
       apply (metis head_atomic_opstep_vis_aact not_tau_aact_iff snd_conv)
      apply (metis head_atomic_opstep_vis_aact not_tau_aact_iff snd_conv)
     apply (simp add: pre_state_def bex_Un, metis)
    apply (simp add: pre_state_def bex_Un, metis)
    done
next
  case (Par \<pi>\<alpha> s ca cb sc')
  then show ?case sorry
next
  case (DoLoop \<pi>\<alpha> s c sc')
  then show ?case sorry
qed fastforce+

lemma all_sec_determ_dopstep_right_completion:
  assumes
    \<open>((sx, c), (sy, c)) =([\<pi>\<alpha>], [])\<Rightarrow> ((sx', c'), (sy, cy))\<close>
    \<open>all_sec_determ c (sx, sy)\<close>
    \<open>(\<Squnion>(set_mset (head_atoms c))) sx =
      (\<Squnion>(set_mset (head_atoms c))) sy\<close>
  shows
    \<open>\<exists>sy'. ((sx, c), (sy, c)) =([\<pi>\<alpha>], [\<pi>\<alpha>])\<Rightarrow> ((sx', c'), (sy', c'))\<close>
  using assms
  by (simp, metis aopstep_equiv_guard_head_state_irrelevant assms(3) eq_fst_iff
      snd_conv)

lemma sync_dopstep_to_opstep:
  \<open>((sx, c), (sy, c)) =([\<pi>\<alpha>], [\<pi>\<alpha>])\<Rightarrow> ((sx', c'), (sy', c')) \<Longrightarrow>
    all_sec_determ c (sx, sy) \<Longrightarrow>
    (exch4 (sx, sy), liftC c) \<midarrow>strip_aact (snd \<pi>\<alpha>)\<rightarrow> (exch4 (sx', sy'), liftC c')\<close>
proof (induct c arbitrary: sx sy sx' sy' c' \<pi>\<alpha>)
  case (Endet c1 c2)
  then show ?case
    apply (case_tac \<open>vis_aact (snd \<pi>\<alpha>)\<close>)
     apply (simp add: vis_tau_aact_incompatible)
     apply (metis fst_conv pre_state_def snd_conv vis_aopstep_impl_atom)
    apply (simp add: vis_tau_aact_incompatible)
    apply (metis head_atomic_opstep_vis_aact not_vis_aact_iff prod_eq_decompose(1))
    done
next
  case (Iter c)
  then show ?case
    apply (case_tac \<open>vis_aact (snd \<pi>\<alpha>)\<close>)
     apply (simp add: vis_tau_aact_incompatible)
    apply (metis comm.inject(1) eq_snd_iff)
    apply (simp add: vis_tau_aact_incompatible del: split_paired_All)
    apply (simp only: head_atomic_nostep_iff_state_not_in_head_guards)
    apply (elim disjE conjE exE; simp)
    subgoal sorry \<comment> \<open> obviously true \<close>
    apply (metis head_atomic_opstep_vis_aact not_tau_aact_iff snd_conv)
    done
qed fastforce+

lemmas sync_dopstep_to_opstepI =
  sync_dopstep_to_opstep[where
    sx=\<open>(lsx,ssx)\<close> and sy=\<open>(lsy,ssy)\<close> and
    sx'=\<open>(lsx',ssx')\<close> and sy'=\<open>(lsy',ssy')\<close>
    for lsx ssx lsy ssy lsx' ssx' lsy' ssy',
    simplified exch4_apply]


lemma aopstep_preserves_all_sec_determ:
  \<open>sc \<midarrow>\<pi>\<alpha>\<rightarrow>\<^sub>a sc' \<Longrightarrow>
    all_sec_determ (snd sc) \<le> all_sec_determ (snd sc')\<close>
proof (induct _ sc sc' rule: aopstep_induct)
  case (Endet \<pi>\<alpha> s ca cb sc')
  then show ?case
    apply clarsimp
    apply (elim disjE conjE)
         apply force
        apply force
       apply (metis head_atomic_opstep_vis_aact not_tau_aact_iff snd_conv)
      apply (metis head_atomic_opstep_vis_aact not_tau_aact_iff snd_conv)
     apply blast
    apply blast
    done
qed fastforce+

lemma dopstep_preserves_all_sec_determ_left:
  \<open>((sx, c), (sy, c)) =(\<rho>x, \<rho>y)\<Rightarrow> ((sx', cx'), (sy', cy')) \<Longrightarrow>
    all_sec_determ c \<le> all_sec_determ cx'\<close>
  using aopstep_preserves_all_sec_determ
  by (force elim!: dopstep.cases)

lemma dopstep_preserves_all_sec_determ_right:
  \<open>((sx, c), (sy, c)) =(\<rho>x, \<rho>y)\<Rightarrow> ((sx', cx'), (sy', cy')) \<Longrightarrow>
    all_sec_determ c \<le> all_sec_determ cy'\<close>
  using aopstep_preserves_all_sec_determ
  by (force elim!: dopstep.cases)

lemma all_sec_determ_same_act_implies_same_comm:
  assumes
    \<open>(sx, c) \<midarrow>\<pi>\<alpha>\<rightarrow>\<^sub>a (sx', cx')\<close>
    \<open>(sy, c) \<midarrow>\<pi>\<alpha>\<rightarrow>\<^sub>a (sy', cy')\<close>
    \<open>all_sec_determ c (sx, sy)\<close>
  shows
    \<open>cy' = cx'\<close>
proof -
  { fix sc sc'
    assume
      \<open>sc \<midarrow>\<pi>\<alpha>\<rightarrow>\<^sub>a sc'\<close>
      \<open>(sy, snd sc) \<midarrow>\<pi>\<alpha>\<rightarrow>\<^sub>a (sy', cy')\<close>
      \<open>all_sec_determ (snd sc) (fst sc, sy)\<close>
    then have \<open>cy' = snd sc'\<close>
    proof (induct _ sc sc' arbitrary: sy sy' cy' rule: aopstep_induct)
      case (Endet \<pi>\<alpha> s ca cb sc')
      then show ?case
        apply simp
        apply (case_tac \<open>vis_aact (snd \<pi>\<alpha>)\<close>)
         apply (clarsimp simp add: vis_tau_aact_incompatible)
        apply (metis (mono_tags) pre_state_def split_pairs2 vis_aopstep_impl_atom)
        apply (simp add: vis_tau_aact_incompatible)
        apply (metis head_atomic_opstep_vis_aact snd_conv tau_aact_def
            vis_aact_simps(2-4))
        done
    next
      case (DoLoop \<pi>\<alpha> s c sc')
      then show ?case
        apply simp
        apply (case_tac \<open>vis_aact (snd \<pi>\<alpha>)\<close>)
        apply (simp, metis snd_conv)
        apply simp
        apply (metis head_atomic_opstep_vis_aact snd_conv tau_aact_def
            vis_aact_simps(2-4))
        done
    qed fastforce+
  }
  then show ?thesis
    using assms
    by fastforce
qed

lemma all_sec_determ_sync_double_step_then_same_result_comm:
  assumes
    \<open>((sx, c), (sy, c)) =([\<pi>\<alpha>], [\<pi>\<alpha>])\<Rightarrow> ((sx', cx'), (sy', cy'))\<close>
    \<open>all_sec_determ c (sx, sy)\<close>
  shows
    \<open>cx' = cy'\<close>
  using assms
    all_sec_determ_same_act_implies_same_comm[where cx'=cx' and cy'=cy']
  by fast


subsection \<open> Safety Implies Security \<close>

theorem safety_implies_security:
  fixes n :: nat
    and cx cy :: \<open>('l::pre_perm_alg \<times> 's) comm\<close>
    and sxy :: \<open>('l, 's) secstate\<close>
    and F I q :: \<open>('l, 's) rgstate \<Rightarrow> bool\<close>
    and R G :: \<open>'s \<times> 's \<Rightarrow> 's \<times> 's \<Rightarrow> bool\<close>
  assumes
    \<open>safe R F G I q n (liftC c) (exch4 sxy)\<close>
    \<open>I \<^emph>\<and> F \<le> all_sec_determ c \<circ> exch4\<close>
  shows
    \<open>secure R F G I q n (c, c) sxy\<close>
  using assms
proof (induct n arbitrary: c sxy)
  case (Suc n)
  note Suc_ih = Suc.hyps[
      where sxy=\<open>((lsx, ssx), (lsy, ssy))\<close> for lsx ssx lsy ssy,
        simplified exch4_apply]
  show ?case
    using Suc.prems
    apply clarsimp
    apply (cases sxy)
    apply clarsimp
    apply (rename_tac lsx ssx lsy ssy)
    apply (elim safe_sucE)
    apply simp
    apply (rule secure_suc)
      (* destructuring *)
         apply (simp; fail)
        apply (simp add: prod_eq_decompose; fail)
      (* term *)
       apply blast
      (* invariant *)
      apply blast
      (* rely *)
     apply (simp add: Suc.hyps; fail)
      (* opstep *)
    apply simp
    apply (drule_tac x=\<open>(fx, fy)\<close> in meta_spec, drule meta_spec2, drule meta_spec2,
        drule meta_mp, (rule conjI; simp; fail))
    apply (drule meta_mp)
     apply simp
     apply (rule sync_dopstep_to_opstepI)
    subgoal sorry
     apply (simp add: le_fun_def sepconj_conj_def imp_ex_conjL; fail)

    oops
    apply (frule sec_determ_dstep_to_opstep)
      apply (simp add: le_fun_def sepconj_conj_def imp_ex_conjL,
        metis all_sec_determ_implies_sec_determ)
     apply clarsimp
    subgoal sorry
    apply (elim disjE conjE exE)
    apply (drule meta_spec2, drule_tac x=\<open>strip_aact (snd \<pi>\<alpha>)\<close> in meta_spec2,
        drule meta_spec2, drule meta_spec2,
        drule meta_mp, (rule conjI; assumption))
    apply simp
    apply (drule meta_mp, assumption)
    apply clarsimp
    apply (frule dopstep_preserves_all_sec_determ_right)
    apply (rename_tac \<pi> \<alpha>\<^sub>a lsx' lsy')
    apply (intro conjI)
      (** guarantee left *)
      apply (clarsimp, metis act.distinct(1) vis_aact_unit_def)
      (** guarantee right *)
     apply (clarsimp, metis act.distinct(1) vis_aact_unit_def)
      (** double-step *)
    apply (frule Suc_ih)
     apply (clarsimp, metis exch4_apply predicate1D)
    apply (rule_tac x=lsx' in exI)
    apply (rule conjI, blast)
    apply (rule conjI, blast)
    apply (rule conjI, force simp add: tau_aact_def)
    apply (rule_tac x=lsy' in exI)
    apply (rule conjI, blast)
    apply (rule conjI, blast)
    apply (rule conjI, force simp add: tau_aact_def)
    apply blast
    done
qed force

end