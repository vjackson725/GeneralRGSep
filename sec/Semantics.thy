 theory Semantics
  imports "../Soundness"
begin

(* TODO: move *)

lemma eqrel_times_eqrel_eq[simp]:
  \<open>((=) \<times>\<^sub>R (=)) = (=)\<close>
  by (force simp add: rel_Times_def)

lemma ex_helpers:
  \<open>(\<exists>c1'. (\<exists>c1. P c1 \<and> c1' = f c1) \<and> Q c1') \<longleftrightarrow> (\<exists>c1. P c1 \<and> Q (f c1))\<close>
  by blast

lemma imp_iff_imp_iff:
  \<open>(A \<longrightarrow> B) = (A \<longrightarrow> C) \<longleftrightarrow> (A \<longrightarrow> B = C)\<close>
  by blast

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
      'l \<times> 's + unit \<Rightarrow>
      nat \<Rightarrow>
      bool\<close>
  where
  pred_executions_nil[intro!]: \<open>pred_executions P F r c (Inl (hl, hs)) 0\<close>
| pred_executions_step[intro]:
  \<open>\<comment> \<open> The config predicate holds \<close>
    P ((hl, hs), c) \<Longrightarrow>
    \<comment> \<open> rely steps generate states \<close>
    (\<And>hs'. r hs hs' \<Longrightarrow> pred_executions P F r c (Inl (hl, hs')) n) \<Longrightarrow>
    \<comment> \<open> framed opsteps generate states \<close>
    (\<And>\<alpha> hlhlf' hs' c' hlf.
        hl ## hlf \<Longrightarrow>
        ((hl + hlf, hs), c) \<midarrow>\<alpha>\<rightarrow> (Inl (hlhlf', hs'), c') \<Longrightarrow>
        F (hlf, hs) \<Longrightarrow>
        (\<exists>hl'.
          hl' ## hlf \<and>
          hlhlf' = hl' + hlf \<and>
          (\<alpha> = Tau \<longrightarrow> hl' = hl) \<and>
          pred_executions P F r c' (Inl (hl', hs')) n)) \<Longrightarrow>
    \<comment> \<open> conclude a step can be made \<close>
    pred_executions P F r c (Inl (hl, hs)) (Suc n)\<close>

subsection \<open> Proofs about safe \<close>

inductive_cases pred_executions_zeroE[elim!]: \<open>pred_executions P F r c z 0\<close>
inductive_cases pred_executions_sucE[elim]: \<open>pred_executions P F r c z (Suc n)\<close>

lemma pred_executions_nil_iff[simp]:
  \<open>pred_executions P F r c z 0 \<longleftrightarrow> (\<exists>hl hs. z = Inl (hl, hs))\<close>
  by force

lemma pred_executions_suc_iff:
  \<open>pred_executions P F r c z (Suc n) \<longleftrightarrow>
    (\<exists>hl hs. z = Inl (hl, hs) \<and>
      P ((hl, hs), c) \<and>
      (\<forall>hs'. r hs hs' \<longrightarrow> pred_executions P F r c (Inl (hl, hs')) n) \<and>
      (\<forall>\<alpha> hlhlf' hs' c' hlf.
          hl ## hlf \<longrightarrow>
          ((hl + hlf,hs), c) \<midarrow>\<alpha>\<rightarrow> (Inl (hlhlf',hs'), c') \<longrightarrow>
          F (hlf, hs) \<longrightarrow>
          (\<exists>hl'.
            hl' ## hlf \<and>
            hlhlf' = hl' + hlf \<and>
            (\<alpha> = Tau \<longrightarrow> hl' = hl) \<and>
            pred_executions P F r c' (Inl (hl', hs')) n)))\<close>
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

nonterminal twoPredLiftL

syntax
  "_twoPredLiftS"  :: "('a \<Rightarrow> bool) \<Rightarrow> twoPredLiftL"  ("\<lblot> _" [0] 1000)
  "_twoPredLiftC"  :: "twoPredLiftL \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool)"  ("_ \<rblot>" [0] 1000)
  "_twoPredLiftL"  :: "twoPredLiftL \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> bool)"  ("_ \<bar>" [0] 1000)
  "_twoPredLiftLR"  :: "twoPredLiftL \<Rightarrow> ('b \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> bool)"  ("_ \<bar> _ \<rblot>" [0] 1000)
  "_twoPredLiftR"  :: "('b \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> bool)"  ("\<bar> _ \<rblot>" [0] 1000)

translations
  "_twoPredLiftC (_twoPredLiftS p)" \<rightharpoonup> "(CONST pred_Times) p p"
  "_twoPredLiftLR (_twoPredLiftS p) q" \<rightleftharpoons> "(CONST pred_Times) p q"
  "_twoPredLiftL (_twoPredLiftS p)" \<rightharpoonup> "(CONST pred_Times) p \<top>"
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
| \<open>(cax \<^bold>+ cay) \<times>\<^sub>C (cbx \<^bold>+ cby) = (cax \<times>\<^sub>C cbx) \<^bold>+ (cay \<times>\<^sub>C cby)\<close>
| \<open>(cax \<box> cay) \<times>\<^sub>C (cbx \<box> cby) = (cax \<times>\<^sub>C cbx) \<box> (cay \<times>\<^sub>C cby)\<close>
| \<open>(DO ca OD) \<times>\<^sub>C (DO cb OD) = DO (ca \<times>\<^sub>C cb) OD\<close>
| \<open>\<langle>pa, qa\<rangle> \<times>\<^sub>C \<langle>pb, qb\<rangle> = \<langle>pa \<times>\<^sub>P pb, qa \<times>\<^sub>R qb\<rangle>\<close>
  by pat_completeness auto (* slow *)

termination
  by (relation \<open>measure (\<lambda>(ca,cb). size ca + size cb)\<close>) simp+


subsection \<open> Double-state Lifting \<close>

(* TODO: move *)
definition diag (\<open>\<Delta>\<close>) where \<open>diag x = (x,x)\<close>
declare diag_def[simp]

abbreviation(input) \<open>liftP p \<equiv> \<lblot> p \<rblot>\<close>
abbreviation(input) \<open>liftR r \<equiv> r \<times>\<^sub>R r\<close>

definition liftC :: \<open>('l \<times> 's) comm \<Rightarrow> (('l \<times> 'l) \<times> ('s \<times> 's)) comm\<close> where
  \<open>liftC c \<equiv> map_comm (\<lambda>p q. (p \<circ> exch4, q \<circ>\<^sub>2 exch4)) (c \<times>\<^sub>C c)\<close>

definition
  \<open>unliftC \<equiv> map_comm (\<lambda>p q. (p \<circ> exch4 \<circ> \<Delta>, q \<circ>\<^sub>2 (exch4 \<circ> \<Delta>)))\<close>

lemma liftC_def':
  \<open>liftC c = map_comm (\<lambda>p q. (liftP p \<circ> exch4, liftR q \<circ>\<^sub>2 exch4)) c\<close>
  unfolding liftC_def
  by (induct c) simp+

lemmas liftC_simps[simp] =
  map_comm.simps[of \<open>(\<lambda>p q. (liftP p \<circ> exch4, liftR q \<circ>\<^sub>2 exch4))\<close>,
    simplified liftC_def'[symmetric]]

lemmas liftC_rev_iff =
  map_comm_rev_iff[of \<open>(\<lambda>p q. (liftP p \<circ> exch4, liftR q \<circ>\<^sub>2 exch4))\<close>,
    simplified liftC_def'[symmetric]]


lemma unlift_lift_cancel[simp]:
  \<open>unliftC (liftC c) = c\<close>
  unfolding unliftC_def liftC_def'
  by (induct c) (simp add: sec_agree_def)+

lemma unliftC_atom_simp:
  \<open>unliftC \<langle>p, q\<rangle> = \<langle>\<lambda>x. p (exch4 (x, x)), \<lambda>x y. q (exch4 (x, x)) (exch4 (y, y))\<rangle>\<close>
  unfolding unliftC_def
  by force

lemmas unliftC_simp[simp] =
  map_comm.simps(1-5,7)[of \<open>(\<lambda>p q. (\<lambda>x. p (exch4 (x,x)), \<lambda>x y. q (exch4 (x,x)) (exch4 (y,y))))\<close>,
    simplified unliftC_def[symmetric]]
  unliftC_atom_simp

lemmas unliftC_rev_iff =
  map_comm_rev_iff[of
    \<open>(\<lambda>p q. (\<lambda>x. p (exch4 (x,x)), \<lambda>x y. q (exch4 (x,x)) (exch4 (y,y))))\<close>,
    simplified unliftC_def[symmetric]]

lemma liftC_cancel[simp]:
  \<open>liftC ca = liftC cb \<longleftrightarrow> ca = cb\<close>
  apply (induct cb arbitrary: ca)
        apply (metis liftC_rev_iff(1))
       apply (metis liftC_rev_iff(2))
      apply (metis liftC_rev_iff(3))
     apply (metis liftC_rev_iff(4))
    apply (metis liftC_rev_iff(5))
   apply (fastforce simp add: liftC_rev_iff fun_eq_iff sec_agree_def)
  apply (metis liftC_rev_iff(6))
  done


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
  \<open>(s, liftC c) \<midarrow>\<alpha>\<rightarrow> (z', cx') \<Longrightarrow> \<exists>c'. cx' = liftC c'\<close>
proof (induct c arbitrary: s z' cx' \<alpha>)
  case Skip
  then show ?case by force
next
  case (Seq c1 c2)
  then show ?case
    by (simp, metis liftC_simps(2))
next
  case (Par c1 c2)
  then show ?case
    by (simp, metis liftC_simps(3))
next
  case (Indet c1 c2)
  then show ?case
    by force
next
  case (Endet c1 c2)
  then show ?case
    using Endet.prems
    by (simp, metis Endet.hyps(2) liftC_simps(5))
next
  case (Atomic x1 x2)
  then show ?case
    apply (clarsimp split: if_splits)
     apply (metis liftC_simps(1))
    apply (metis liftC_rev_iff(7))
    done
next
  case (Iter c)
  then show ?case
    by (clarsimp split: if_splits, metis liftC_simps(1), metis liftC_simps(2,7))
qed

theorem weak_noninterference:
  \<open>safe n c z r g q S F \<Longrightarrow>
    z = Inl s \<Longrightarrow>
    c = liftC cx \<Longrightarrow>
    S \<^emph>\<and> F \<le> \<bbbA> \<oo> \<circ> exch4 \<Longrightarrow>
    tree_weak_noninterference \<oo> F r c z n\<close>
  apply (induct arbitrary: s cx rule: safe.inducts)
   apply force
  apply (clarsimp simp add: liftC_rev_iff pred_executions_suc_iff)
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


(*
    (\<forall>c1 c2. c = c1 \<box> c2 \<or> c = c1 \<^bold>+ c2 \<longrightarrow>
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

datatype 'a pact = PL \<open>'a pact\<close> | PR \<open>'a pact\<close> | Act 'a

fun strip_pact :: \<open>'a act pact \<Rightarrow> 'a act\<close> where
  \<open>strip_pact (Act \<alpha>) = \<alpha>\<close>
| \<open>strip_pact (PL \<beta>) = strip_pact \<beta>\<close>
| \<open>strip_pact (PR \<beta>) = strip_pact \<beta>\<close>

fun act_pact :: \<open>'a act pact \<Rightarrow> 'a act\<close> where
  \<open>act_pact (Act \<alpha>) = \<alpha>\<close>
| \<open>act_pact _ = undefined\<close>


text \<open>
  In a pact, a tau move may be buried under parallel synchronisation labels.
  In programs where sub-programs may take actions (\<box>), we need an
  inductive test for whether an action is internal, as the sub-program may be a parallel.
\<close>
definition \<open>tau_pact \<beta> \<equiv> strip_pact \<beta> = Tau\<close>

definition \<open>vis_pact \<beta> \<equiv> \<exists>u. strip_pact \<beta> = Vis u\<close>

lemma not_tau_pact_iff[simp]:
  \<open>\<not> tau_pact \<beta> \<longleftrightarrow> vis_pact \<beta>\<close>
  by (simp add: tau_pact_def vis_pact_def)

lemma not_vis_pact_iff[simp]:
  \<open>\<not> vis_pact \<beta> \<longleftrightarrow> tau_pact \<beta>\<close>
  by (simp add: tau_pact_def vis_pact_def)

lemma vis_tau_pact_incompatible:
  \<open>vis_pact \<beta> \<Longrightarrow> tau_pact \<beta> = False\<close>
  \<open>tau_pact \<beta> \<Longrightarrow> vis_pact \<beta> = False\<close>
  by (simp add: tau_pact_def vis_pact_def)+

lemma vis_pact_unit_def:
  \<open>vis_pact \<beta> \<longleftrightarrow> strip_pact \<beta> = Vis ()\<close>
  by (simp add: vis_pact_def)

lemma vis_pact_simps[simp]:
  \<open>vis_pact (PL \<beta>) \<longleftrightarrow> vis_pact \<beta>\<close>
  \<open>vis_pact (PR \<beta>) \<longleftrightarrow> vis_pact \<beta>\<close>
  \<open>vis_pact (Act \<alpha>) \<longleftrightarrow> (\<exists>u. \<alpha> = Vis u)\<close>
  by (simp add: vis_pact_def)+

lemma tau_pact_simps[simp]:
  \<open>tau_pact (PL \<beta>) \<longleftrightarrow> tau_pact \<beta>\<close>
  \<open>tau_pact (PR \<beta>) \<longleftrightarrow> tau_pact \<beta>\<close>
  \<open>tau_pact (Act \<alpha>) \<longleftrightarrow> \<alpha> = Tau\<close>
  by (simp add: tau_pact_def)+


subsection \<open> Parallel Opstep \<close>

text \<open>
  Unfortunately, because acts are often universally quantified,
  using a general type variable becomes prohibitively unwieldy.
  (Due to \<open>itself\<close> types and schematics type vars in \<open>induct\<close>.)
  Thus we just use unit.
\<close>
fun popstep :: \<open>unit act pact \<Rightarrow> 's pconfig \<Rightarrow> 's cpconfig \<Rightarrow> bool\<close> where
  \<open>popstep \<beta> (h, Skip) s' \<longleftrightarrow> False\<close>
| \<open>popstep \<beta> (h, c1 ;; c2) s' \<longleftrightarrow>
    \<beta> = Act Tau \<and> c1 = Skip \<and> s' = (Inl h, c2) \<or>
    (\<exists>h' c1'. popstep \<beta> (h,c1) (h',c1') \<and> s' = (h', c1' ;; c2))\<close>
| \<open>popstep \<beta> (h, c1 \<^bold>+ c2) s' \<longleftrightarrow>
    \<beta> = Act Tau \<and> s' = (Inl h, c1) \<or>
    \<beta> = Act Tau \<and> s' = (Inl h, c2)\<close>
| \<open>popstep \<beta> (h, c1 \<box> c2) s' \<longleftrightarrow>
    (\<beta> = Act Tau \<and> c1 = Skip \<and> s' = (Inl h, c2) \<or>
      \<beta> = Act Tau \<and> c2 = Skip \<and> s' = (Inl h, c1) \<or>
      (if tau_pact \<beta> then
        (\<exists>h' c1'. s' = (h', c1' \<box> c2) \<and> popstep \<beta> (h, c1) (h', c1')) \<or>
        (\<exists>h' c2'. s' = (h', c1 \<box> c2') \<and> popstep \<beta> (h, c2) (h', c2'))
      else
        popstep \<beta> (h, c1) s' \<or> popstep \<beta> (h, c2) s'))\<close>
| \<open>popstep \<beta> (h, c1 \<parallel> c2) s' \<longleftrightarrow>
    \<beta> = Act Tau \<and> c1 = Skip \<and> c2 = Skip \<and> s' = (Inl h, Skip) \<or>
    (\<exists>\<beta>x. \<beta> = PL \<beta>x \<and> (\<exists>h' c1'. popstep \<beta>x (h,c1) (h',c1') \<and> s' = (h', c1' \<parallel> c2))) \<or>
    (\<exists>\<beta>x. \<beta> = PR \<beta>x \<and> (\<exists>h' c2'. popstep \<beta>x (h,c2) (h',c2') \<and> s' = (h', c1 \<parallel> c2')))\<close>
| \<open>popstep \<beta> (h, DO c OD) s' \<longleftrightarrow>
      ((\<forall>h' c'. \<not> popstep \<beta> (h, c) (Inl h', c')) \<and>
        \<beta> = Act Tau \<and> s' = (Inl h, Skip)) \<or>
      (\<exists>h' c'.
        popstep \<beta> (h, c) (Inl h', c') \<and>
        s' = (Inl h', c' ;; DO c OD)) \<or>
      ((\<exists>c'. popstep \<beta> (h, c) (Inr (), c')) \<and>
        s' = (Inr (), DO c OD))\<close>
| \<open>popstep \<beta> (h, Atomic ap aq) s' \<longleftrightarrow>
    (\<exists>a. \<beta> = Act (Vis a) \<and>
          (if ap h
            then \<exists>h'. aq h h' \<and> fst s' = Inl h' \<and> snd s' = Skip
            else fst s' = Inr () \<and> snd s' = Atomic ap aq))\<close>

lemmas popstep_induct = popstep.induct[case_names Skip Seq Indet Endet Par DoLoop Atom]
hide_fact popstep.induct


paragraph \<open> Pretty parallel operational semantics \<close>

text \<open> \<open>sc\<close> can step to \<open>zc'\<close> \<close>
abbreviation pretty_popstep :: \<open>_ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> _\<close> (\<open>_ \<midarrow>(_)\<rightarrow>\<^sub>p _\<close> [60,0,60] 60) where
  \<open>sc \<midarrow>\<beta>\<rightarrow>\<^sub>p zc' \<equiv> popstep \<beta> sc zc'\<close>

text \<open> no steps from \<open>sc\<close> can take place, except perhaps crashes \<close>
abbreviation pretty_no_good_popstep :: \<open>'s \<times> 's comm \<Rightarrow> bool\<close> (\<open>_ \<midarrow>'/\<rightarrow>\<^sub>p\<close> [60] 60) where
  \<open>sc \<midarrow>/\<rightarrow>\<^sub>p \<equiv> \<forall>\<beta> s' c'. \<not> popstep \<beta> sc (Inl s', c')\<close>

text \<open> no steps from \<open>sc\<close> can take place at all \<close>
abbreviation pretty_no_popstep :: \<open>'s \<times> 's comm \<Rightarrow> bool\<close> (\<open>_ \<midarrow>\<sslash>\<rightarrow>\<^sub>p\<close> [60] 60) where
  \<open>sc \<midarrow>\<sslash>\<rightarrow>\<^sub>p \<equiv> \<forall>\<beta> zc'. \<not> popstep \<beta> sc zc'\<close>


subsubsection \<open> popstep lemmas \<close>

lemma popstep_tau_preserves_state:
  \<open>sc \<midarrow>\<beta>\<rightarrow>\<^sub>p zc' \<Longrightarrow> tau_pact \<beta> \<Longrightarrow> fst zc' = Inl (fst sc)\<close>
  by (induct rule: popstep_induct)
    (fastforce split: if_splits simp add: tau_pact_def)+

lemma no_opstep_then_no_popstep:
  \<open>sc \<midarrow>|\<rightarrow> \<Longrightarrow> sc \<midarrow>\<sslash>\<rightarrow>\<^sub>p\<close>
  apply (induct rule: popstep_induct)
        apply (clarsimp split: if_splits; fail)
       apply (clarsimp simp add: all_conj_distrib disj_imp split: if_splits; fail)
      apply fastforce
     apply (clarsimp simp add: all_conj_distrib disj_imp split: if_splits)
     apply (subgoal_tac \<open>(\<forall>\<alpha> a b. \<not> (h, c1) \<midarrow>\<alpha>\<rightarrow> (a, b)) \<and> (\<forall>\<alpha> a b. \<not> (h, c2) \<midarrow>\<alpha>\<rightarrow> (a, b))\<close>)
      prefer 2
      apply (metis (full_types) unit.exhaust opstep_act_cases)
     apply (case_tac \<open>strip_pact \<beta>\<close>; force)
    apply (clarsimp simp add: all_conj_distrib disj_imp split: if_splits; fail)
   apply (clarsimp simp add: all_conj_distrib split: if_splits, blast)
  apply (simp; fail)
  done

lemma no_popstep_then_no_opstep:
  \<open>sc \<midarrow>\<sslash>\<rightarrow>\<^sub>p \<Longrightarrow> sc \<midarrow>|\<rightarrow>\<close>
  apply (induct rule: popstep_induct)
        apply (clarsimp split: if_splits; fail)
       apply (clarsimp simp add: all_conj_distrib disj_imp split: if_splits; fail)
      apply fastforce
     apply (clarsimp simp add: all_conj_distrib disj_imp split: if_splits)
     apply (case_tac \<open>strip_pact \<beta>\<close>)
      apply (metis not_vis_pact_iff)
     apply (clarsimp, metis not_vis_pact_iff)
    apply (clarsimp, metis)
   apply (clarsimp, metis)
  apply force
  done

lemma strip_popstep:
  \<open>sc \<midarrow>\<beta>\<rightarrow>\<^sub>p zc' \<Longrightarrow> sc \<midarrow>strip_pact \<beta>\<rightarrow> zc'\<close>
  apply (induct \<beta> sc zc' rule: popstep_induct)
        apply fastforce
       apply fastforce
      apply fastforce
  subgoal sorry
    apply (clarsimp, metis act.distinct(1) strip_pact.simps(1-3))
   apply clarsimp
(* TODO: haven't updated the original definition yet *)
(*
   apply (force simp add: no_popstep_then_no_opstep split: if_splits)
*)
  subgoal sorry
  apply force
  sorry

lemma vis_popstep_impl_atom:
  \<open>sc \<midarrow>\<beta>\<rightarrow>\<^sub>p zc' \<Longrightarrow>
    vis_pact \<beta> \<Longrightarrow>
    \<exists>p q.
      (p, q) \<in> head_atoms (snd sc) \<and>
      (p (fst sc) \<longrightarrow> (\<exists>s'. fst zc' = Inl s' \<and> q (fst sc) s')) \<and>
      (\<not> p (fst sc) \<longrightarrow> fst zc' = Inr ())\<close>
  apply (induct rule: popstep_induct)
        apply fastforce
       apply fastforce
      apply fastforce
    (* Endet *)
     apply (clarsimp simp add: vis_pact_def tau_pact_def)
     apply (elim disjE)
        apply force
       apply force
      apply metis
     apply metis
    (* Parallel *)
    apply (clarsimp simp add: vis_pact_def tau_pact_def)
    apply (elim disjE)
      apply force
     apply (clarsimp, metis)
    apply (clarsimp, metis)
    (* DoLoop *)
   apply fastforce
    (* Atom *)
  apply fastforce
  done

lemma popstep_then_popstep_right_seqD:
  \<open>sc \<midarrow>\<beta>\<rightarrow>\<^sub>p zc' \<Longrightarrow>
    sc = (s, c) \<Longrightarrow>
    zc' = (Inl s', c') \<Longrightarrow>
    (s, c ;; cx) \<midarrow>\<beta>\<rightarrow>\<^sub>p (Inl s', c' ;; cx)\<close>
  by (induct \<beta> sc zc' arbitrary: s c s' c' rule: popstep_induct) simp+

lemma popstep_then_popstep_right_endetD:
  \<open>sc \<midarrow>\<beta>\<rightarrow>\<^sub>p zc' \<Longrightarrow>
    sc = (s, c) \<Longrightarrow>
    zc' = (Inl s', c') \<Longrightarrow>
    (vis_pact \<beta> \<longrightarrow> (s, c \<box> cb) \<midarrow>\<beta>\<rightarrow>\<^sub>p (Inl s', c')) \<and>
    (tau_pact \<beta> \<longrightarrow> (s, c \<box> cb) \<midarrow>\<beta>\<rightarrow>\<^sub>p (Inl s', c' \<box> cb))\<close>
  by (induct \<beta> sc zc' arbitrary: s c s' c' rule: popstep_induct)
    (simp add: vis_pact_def tau_pact_def)+

lemma popstep_then_popstep_left_endetD:
  \<open>sc \<midarrow>\<beta>\<rightarrow>\<^sub>p zc' \<Longrightarrow>
    sc = (s, c) \<Longrightarrow>
    zc' = (Inl s', c') \<Longrightarrow>
    (vis_pact \<beta> \<longrightarrow> (s, ca \<box> c) \<midarrow>\<beta>\<rightarrow>\<^sub>p (Inl s', c')) \<and>
    (tau_pact \<beta> \<longrightarrow> (s, ca \<box> c) \<midarrow>\<beta>\<rightarrow>\<^sub>p (Inl s', ca \<box> c'))\<close>
  by (induct \<beta> sc zc' arbitrary: s c s' c' rule: popstep_induct)
    (simp add: vis_pact_def tau_pact_def)+

lemma popstep_then_popstep_doloopD:
  \<open>sc \<midarrow>\<beta>\<rightarrow>\<^sub>p zc' \<Longrightarrow>
    sc = (s, c) \<Longrightarrow>
    zc' = (Inl s', c') \<Longrightarrow>
    (s, DO c OD) \<midarrow>\<beta>\<rightarrow>\<^sub>p (Inl s', c' ;; DO c OD)\<close>
  by (induct \<beta> sc zc' arbitrary: s c s' c' rule: popstep_induct) simp+

lemma popstep_pact_cases:
  \<open>sc \<midarrow>\<beta>\<rightarrow>\<^sub>p zc' \<Longrightarrow>
    (sc \<midarrow>\<beta>\<rightarrow>\<^sub>p zc' \<Longrightarrow> vis_pact \<beta> \<Longrightarrow> P) \<Longrightarrow>
    (sc \<midarrow>\<beta>\<rightarrow>\<^sub>p zc' \<Longrightarrow> tau_pact \<beta> \<Longrightarrow> fst zc' = Inl (fst sc) \<Longrightarrow> P) \<Longrightarrow>
    P\<close>
  unfolding vis_pact_def tau_pact_def
  using not_vis_pact_iff popstep_tau_preserves_state tau_pact_def vis_pact_unit_def by blast


subsection \<open> endet cluster \<close>

fun endet_cluster :: \<open>'a comm \<Rightarrow> 'a comm set\<close> where
  \<open>endet_cluster Skip = {Skip}\<close>
| \<open>endet_cluster (ca ;; cb) = {ca ;; cb}\<close>
| \<open>endet_cluster (ca \<parallel> cb) = {ca \<parallel> cb}\<close>
| \<open>endet_cluster (ca \<^bold>+ cb) = {ca \<^bold>+ cb}\<close>
| \<open>endet_cluster (ca \<box> cb) = (endet_cluster ca \<union> endet_cluster cb)\<close>
| \<open>endet_cluster (\<langle>p, q\<rangle>) = {\<langle>p, q\<rangle>}\<close>
| \<open>endet_cluster (DO c OD) = {DO c OD}\<close>

lemma in_endet_cluster_then_subcomm:
  \<open>ca \<in> endet_cluster c \<Longrightarrow> if \<exists>cx cy. c = cx \<box> cy then ca < c else ca \<le> c\<close>
  by (induct c arbitrary: ca)
    (fastforce simp add: if_bool_eq_disj del: disjCI)+

lemma endet_cluster_never_endet[simp]:
  \<open>ca \<box> cb \<notin> endet_cluster c\<close>
  by (induct c) fastforce+


subsection \<open> Self-popstep Impossible \<close>

lemma self_popstep_impossible:
  \<open>(s, c) \<midarrow>\<beta>\<rightarrow>\<^sub>p (Inl s', c) \<longleftrightarrow> False\<close>
  apply (induct c arbitrary: \<beta> s s')
        apply (simp; fail)+
    apply clarsimp
  subgoal sorry
   apply (simp; fail)+
  done

lemma popstep_endet_skip_then:
  \<open>(s, c \<box> Skip) \<midarrow>\<beta>\<rightarrow>\<^sub>p (Inl s', c) \<Longrightarrow> tau_pact \<beta> \<and> s' = s\<close>
  \<open>(s, Skip \<box> c) \<midarrow>\<beta>\<rightarrow>\<^sub>p (Inl s', c) \<Longrightarrow> tau_pact \<beta> \<and> s' = s\<close>
  by (metis tau_pact_def popstep_tau_preserves_state self_popstep_impossible
      fst_conv popstep.simps(1,4) strip_pact.simps(1) sum.inject(1))+


section \<open> Extended step \<close>

datatype 'a eact =
  Env
  | Crash 'a
  | Loc 'a

lemma eact_eq_iff[simp]:
  \<open>Env = Crash a \<longleftrightarrow> False\<close>
  \<open>Crash a = Env \<longleftrightarrow> False\<close>
  \<open>Loc a = Crash b \<longleftrightarrow> False\<close>
  \<open>Crash a = Loc b \<longleftrightarrow> False\<close>
  by force+


definition
  \<open>estep r F \<equiv>
    \<lambda>\<beta>. case \<beta> of Env \<Rightarrow>
      (\<lambda>((xl,xs),c) (mx', c').
        c' = c \<and>
        (\<exists>xs'.
          mx' = Inl (xl, xs') \<and>
          r xs xs' \<and>
          (\<exists>xf. F (xf, xs) \<and> xl ## xf) \<and>
          (\<exists>xf'. F (xf', xs') \<and> xl ## xf')))
      | Loc \<beta> \<Rightarrow>
        (\<lambda>((xl,xs),c) (mx',c').
          \<exists>xf.
            F (xf, xs) \<and>
            xl ## xf \<and>
            (\<exists>mxf'.
              popstep \<beta> ((xl + xf,xs),c) (mxf', c') \<and>
              (\<exists>xl' xlf' xs'.
                mxf' = Inl (xlf', xs') \<and>
                F (xf, xs') \<and>
                xl' ## xf \<and>
                xlf' = xl' + xf \<and>
                mx' = Inl (xl', xs'))))
      | Crash \<beta> \<Rightarrow>
        (\<lambda>((xl,xs),c) (mx',c').
          \<exists>xf.
            F (xf, xs) \<and>
            xl ## xf \<and>
            popstep \<beta> ((xl + xf,xs),c) (Inr (), c') \<and>
            mx' = Inr ())\<close>

paragraph \<open> Pretty extended extended opsem \<close>

abbreviation pretty_estep :: \<open>_ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> bool\<close> (\<open>_ \<midarrow>(_, _, _)\<rightarrow>\<^sub>e _\<close> [60,0,0,0,60] 60) where
  \<open>sc \<midarrow>r, F, \<gamma>\<rightarrow>\<^sub>e zc' \<equiv> estep r F \<gamma> sc zc'\<close>

abbreviation pretty_no_estep :: \<open>_ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> bool\<close> (\<open>_ \<midarrow>_, _, |\<rightarrow>\<^sub>e\<close> [60, 0, 0] 60) where
  \<open>sc \<midarrow>r, F, |\<rightarrow>\<^sub>e \<equiv> \<forall>\<gamma> zc'. \<not> estep r F \<gamma> sc zc'\<close>


subsection \<open> Lemmas about estep \<close>

lemma estep_simps[simp]:
  \<open>estep r F Env sc zc' =
    (snd zc' = snd sc \<and>
      (\<exists>xs'.
        fst zc' = Inl (fst (fst sc), xs') \<and>
        r (snd (fst sc)) xs' \<and>
        (\<exists>xf. F (xf, snd (fst sc)) \<and> fst (fst sc) ## xf) \<and>
        (\<exists>xf'. F (xf', xs') \<and> fst (fst sc) ## xf')))\<close>
  \<open>estep r F (Loc \<beta>) sc zc' =
    (\<exists>xf.
      F (xf, snd (fst sc)) \<and>
      fst (fst sc) ## xf \<and>
      (\<exists>mxf'.
        popstep \<beta> ((fst (fst sc) + xf, snd (fst sc)), snd sc) (mxf', snd zc') \<and>
        (\<exists>xl' xs'.
          xl' ## xf \<and>
          mxf' = Inl (xl' + xf, xs') \<and>
          F (xf, xs') \<and>
          fst zc' = Inl (xl', xs'))))\<close>
  \<open>estep r F (Crash \<beta>) sc zc' =
    (\<exists>xf.
      F (xf, snd (fst sc)) \<and>
      fst (fst sc) ## xf \<and>
      popstep \<beta> ((fst (fst sc) + xf, snd (fst sc)), snd sc) (Inr (), snd zc') \<and>
      fst zc' = Inr ())\<close>
  by (force simp add: estep_def split: sum.splits unit.splits prod.splits)+

lemma estepE[elim]:
  \<open>estep r F \<gamma> sc zc' \<Longrightarrow>
    (\<And>xl xs c xs' xf xf'.
      sc = ((xl, xs), c) \<Longrightarrow>
      zc' = (Inl (xl, xs'), c) \<Longrightarrow>
      r xs xs' \<Longrightarrow>
      F (xf, xs) \<Longrightarrow>
      xl ## xf \<Longrightarrow>
      F (xf', xs') \<Longrightarrow>
      xl ## xf' \<Longrightarrow>
      P) \<Longrightarrow>
    (\<And>\<beta> xl xs c mx' c' xf mxf'.
      \<gamma> = Loc \<beta> \<Longrightarrow>
      sc = ((xl,xs),c) \<Longrightarrow>
      zc' = (mx',c') \<Longrightarrow>
      F (xf, xs) \<Longrightarrow>
      xl ## xf \<Longrightarrow>
      popstep \<beta> ((xl + xf,xs),c) (mxf', c') \<and>
      (\<exists>xl' xlf' xs'.
        mxf' = Inl (xlf', xs') \<and>
        F (xf, xs') \<and>
        xl' ## xf \<and>
        xlf' = xl' + xf \<and>
        mx' = Inl (xl', xs')) \<or>
      (mxf' = Inr () \<and> mx' = Inr()) \<Longrightarrow>
      P) \<Longrightarrow>
    P\<close>
  sorry
(*
  by (cases sc, cases zc', cases \<gamma>; force)
*)

lemma estep_def':
  \<open>estep r F \<gamma> sc zc' \<longleftrightarrow>
    \<gamma> = Env \<and>
      snd zc' = snd sc \<and>
      (\<exists>xs'.
        fst zc' = Inl (fst (fst sc), xs') \<and>
        r (snd (fst sc)) xs' \<and>
        (\<exists>xf. F (xf, snd (fst sc)) \<and> fst (fst sc) ## xf) \<and>
        (\<exists>xf'. F (xf', xs') \<and> fst (fst sc) ## xf')) \<or>
    (\<exists>\<beta>. \<gamma> = Loc \<beta> \<and>
      (\<exists>xf.
      F (xf, snd (fst sc)) \<and>
      fst (fst sc) ## xf \<and>
      (\<exists>mxf'.
        popstep \<beta> ((fst (fst sc) + xf, snd (fst sc)), snd sc) (mxf', snd zc') \<and>
        ((\<exists>xl' xs'.
          xl' ## xf \<and>
          mxf' = Inl (xl' + xf, xs') \<and>
          F (xf, xs') \<and>
          fst zc' = Inl (xl', xs')) \<or>
        (mxf' = Inr () \<and> fst zc' = Inr ())))))\<close>
(*
  by (force simp add: estep_def split: sum.splits unit.splits prod.splits)
*)
  sorry

lemma estep_skip_iff[simp]:
  \<open>estep r F \<gamma> (s, Skip) zc' \<longleftrightarrow> 
    \<gamma> = Env \<and>
    (\<exists>xs'.
      zc' = (Inl (fst s, xs'), Skip) \<and>
      fst zc' = Inl (fst s, xs') \<and>
      r (snd s) xs' \<and>
      (\<exists>xf. F (xf, snd s) \<and> fst s ## xf) \<and>
      (\<exists>xf'. F (xf', xs') \<and> fst s ## xf'))\<close>
  by (force simp add: estep_def split: prod.splits eact.splits)

lemma estep_crash_iff[simp]:
  \<open>estep r F \<gamma> sc (Inr (), c') \<longleftrightarrow>
    (\<exists>\<beta>. \<gamma> = Crash \<beta> \<and>
      (\<exists>xf.
        F (xf, snd (fst sc)) \<and>
        fst (fst sc) ## xf \<and>
        popstep \<beta> ((fst (fst sc) + xf, snd (fst sc)), snd sc) (Inr (), c')))\<close>
  by (clarsimp simp add: estep_def split: prod.splits eact.splits)

lemma estep_then_estep_right_par:
  \<open>(s, c) \<midarrow>r, F, \<gamma>\<rightarrow>\<^sub>e (Inl s', c') \<Longrightarrow>
    (s, c \<parallel> cb) \<midarrow>r, F, map_eact PL \<gamma>\<rightarrow>\<^sub>e (Inl s', c' \<parallel> cb)\<close>
  unfolding estep_def
  by (clarsimp split: prod.splits eact.splits)

lemma estep_then_estep_left_par:
  \<open>(s, c) \<midarrow>r, F, \<gamma>\<rightarrow>\<^sub>e (Inl s', c') \<Longrightarrow>
    (s, ca \<parallel> c) \<midarrow>r, F, map_eact PR \<gamma>\<rightarrow>\<^sub>e (Inl s', ca \<parallel> c')\<close>
  unfolding estep_def
  by (clarsimp split: prod.splits eact.splits)

lemma estep_then_estep_right_endet:
  \<open>(s, c) \<midarrow>r, F, \<gamma>\<rightarrow>\<^sub>e (Inl s', c') \<Longrightarrow>
    (\<forall>\<beta>. \<gamma> = Env \<longrightarrow> (s, c \<box> cb) \<midarrow>r, F, \<gamma>\<rightarrow>\<^sub>e (Inl s', c' \<box> cb)) \<and>
    (\<forall>\<beta>. \<gamma> = Loc \<beta> \<longrightarrow>
      (vis_pact \<beta> \<longrightarrow> (s, c \<box> cb) \<midarrow>r, F, \<gamma>\<rightarrow>\<^sub>e (Inl s', c')) \<and>
      (tau_pact \<beta> \<longrightarrow> (s, c \<box> cb) \<midarrow>r, F, \<gamma>\<rightarrow>\<^sub>e (Inl s', c' \<box> cb)))\<close>
  unfolding estep_def
  by (force split: prod.splits simp add: vis_pact_def tau_pact_def)

lemma estep_then_estep_left_endet:
  \<open>(s, c) \<midarrow>r, F, \<gamma>\<rightarrow>\<^sub>e (Inl s', c') \<Longrightarrow>
    (\<forall>\<beta>. \<gamma> = Env \<longrightarrow> (s, ca \<box> c) \<midarrow>r, F, \<gamma>\<rightarrow>\<^sub>e (Inl s', ca \<box> c')) \<and>
    (\<forall>\<beta>. \<gamma> = Loc \<beta> \<longrightarrow>
      (vis_pact \<beta> \<longrightarrow> (s, ca \<box> c) \<midarrow>r, F, \<gamma>\<rightarrow>\<^sub>e (Inl s', c')) \<and>
      (tau_pact \<beta> \<longrightarrow> (s, ca \<box> c) \<midarrow>r, F, \<gamma>\<rightarrow>\<^sub>e (Inl s', ca \<box> c')))\<close>
  unfolding estep_def
  by (force split: prod.splits simp add: vis_pact_def tau_pact_def)

lemma estep_then_estep_doloop:
  \<open>(s, c) \<midarrow>r, F, \<gamma>\<rightarrow>\<^sub>e (Inl s', c') \<Longrightarrow>
    (\<forall>\<beta>. \<gamma> = Env \<longrightarrow> (s, DO c OD) \<midarrow>r, F, \<gamma>\<rightarrow>\<^sub>e (Inl s', DO c' OD)) \<and>
    (\<forall>\<beta>. \<gamma> = Loc \<beta> \<longrightarrow> (s, DO c OD) \<midarrow>r, F, \<gamma>\<rightarrow>\<^sub>e (Inl s', c' ;; DO c OD))\<close>
  unfolding estep_def
  by (force split: prod.splits)


subsection \<open> Extended steps \<close>

inductive esteps :: \<open>_ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> bool\<close> where
  nil: \<open>c' = c \<Longrightarrow> z' = Inl s \<Longrightarrow> esteps r F [] (s, c) (z', c')\<close>
| crashstep: \<open>
  estep r F \<gamma> (s, c) (Inr (), c'') \<Longrightarrow>
    z'' = Inr () \<Longrightarrow>
    esteps r F [\<gamma>] (s, c) (z'', c'')\<close>
| opstep: \<open>
  estep r F \<gamma> (s, c) (Inl s', c') \<and>
  esteps r F \<gamma>s (s', c') (z'', c'') \<Longrightarrow>
  esteps r F (\<gamma> # \<gamma>s) (s, c) (z'', c'')\<close>


inductive_cases esteps_nilE[elim!]: \<open>esteps r F [] sc zc'\<close>
inductive_cases esteps_consE[elim]: \<open>esteps r F (\<gamma> # \<gamma>s) sc zc'\<close>

abbreviation esteps_pretty :: \<open>_ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> bool\<close>
  (\<open>_ \<midarrow>_, _, _\<rightarrow>\<^sub>e\<^sup>* _\<close> [50, 0, 0, 50])
  where
    \<open>sc \<midarrow>r, F, \<gamma>s\<rightarrow>\<^sub>e\<^sup>* zc' \<equiv> esteps r F \<gamma>s sc zc'\<close>


section \<open> Double Step \<close>

inductive dstep
  :: \<open>('s \<times> 's \<Rightarrow> 's \<times> 's \<Rightarrow> bool) \<Rightarrow>
        (('l::pre_perm_alg \<times> 'l) \<times> ('s \<times> 's) \<Rightarrow> bool) \<Rightarrow>
        _ eact \<times> _ eact \<Rightarrow>
        _ \<Rightarrow> _ \<Rightarrow> bool\<close>
  where
  \<open>rr (sx,sy) (sx',sy') \<Longrightarrow>
    dstep rr FF (Env, Env)
      (((lx,sx),cx), ((ly,sy),cy))
      ((Inl (lx, sx'),cx), (Inl (ly,sy'),cy))\<close>
| \<open>FF ((fx,fy),(sx,sy)) \<Longrightarrow>
    lx ## fx \<Longrightarrow>
    ly ## fy \<Longrightarrow>
    popstep \<beta>x ((lx+fx,sx),cx) (Inl (lx' + fx, sx'), cx') \<Longrightarrow>
    popstep \<beta>y ((ly+fy,sy),cy) (Inl (ly' + fy, sy'), cy') \<Longrightarrow>
    lx' ## fx \<Longrightarrow>
    ly' ## fy \<Longrightarrow>
    FF ((fx,fy), (sx',sy')) \<Longrightarrow>
    dstep rr FF (Loc \<beta>x, Loc \<beta>y)
      (((lx,sx),cx), ((ly,sy),cy))
      ((Inl (lx', sx'),cx'), (Inl (ly', sy'),cy'))\<close>
| \<open>FF ((fx,fy),(sx,sy)) \<Longrightarrow>
    lx ## fx \<Longrightarrow>
    ly ## fy \<Longrightarrow>
    popstep \<beta>x ((lx+fx,sx),cx) (Inr (), cx') \<Longrightarrow>
    popstep \<beta>y ((ly+fy,sy),cy) (Inr (), cy') \<Longrightarrow>
    dstep rr FF (Crash \<beta>x, Crash \<beta>y)
      (((lx,sx),cx), ((ly,sy),cy))
      ((Inr (),cx'), (Inr (),cy'))\<close>

inductive_cases dstep_EnvEnvE[elim!]: \<open>dstep rr FF (Env, Env) ss zz'\<close>
inductive_cases dstep_LocLocE[elim!]: \<open>dstep rr FF (Loc \<beta>x, Loc \<beta>y) ss zz'\<close>
inductive_cases dstep_CrashCrashE[elim!]: \<open>dstep rr FF (Crash \<beta>x, Crash \<beta>y) ss zz'\<close>

inductive_cases dstep_EnvLocE[elim!]: \<open>dstep rr FF (Env, Loc \<beta>y) ss zz'\<close>
inductive_cases dstep_EnvCrashE[elim!]: \<open>dstep rr FF (Env, Crash \<beta>y) ss zz'\<close>
inductive_cases dstep_LocEnvE[elim!]: \<open>dstep rr FF (Loc \<beta>x, Env) ss zz'\<close>
inductive_cases dstep_LocCrashE[elim!]: \<open>dstep rr FF (Loc \<beta>x, Crash \<beta>y) ss zz'\<close>
inductive_cases dstep_CrashEnvE[elim!]: \<open>dstep rr FF (Crash \<beta>x, Env) ss zz'\<close>
inductive_cases dstep_CrashLocE[elim!]: \<open>dstep rr FF (Crash \<beta>x, Loc \<beta>y) ss zz'\<close>

abbreviation pretty_dstep :: \<open>_ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> bool\<close> (\<open>_ =_, _, _\<Rightarrow> _\<close> [55, 0, 55]) where
  \<open>cc =rr, FF, \<gamma>\<gamma>\<Rightarrow> cc' \<equiv> dstep rr FF \<gamma>\<gamma> cc cc'\<close>

inductive dsteps :: \<open>_ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> bool\<close> where
  nil:
  \<open>zz' = ((Inl (fst (fst ss)), snd (fst ss)), (Inl (fst (snd ss)), snd (snd ss))) \<Longrightarrow>
    dsteps r F [] ss zz'\<close>
| step:
  \<open>dstep r F \<gamma> ss ((Inl sx', cy'), (Inl sy', cy')) \<Longrightarrow>
    dsteps r F \<gamma>s ((sx', cy'), (sy', cy')) zz'' \<Longrightarrow>
    dsteps r F (\<gamma> # \<gamma>s) ss zz''\<close>

inductive_cases dsteps_nilE[elim!]: \<open>dsteps r F [] sc zc'\<close>
inductive_cases dsteps_consE[elim]: \<open>dsteps r F (\<gamma> # \<gamma>s) sc zc'\<close>

abbreviation dsteps_pretty :: \<open>_ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> bool\<close>
  (\<open>_ =_, _, _\<Rightarrow>\<^sup>* _\<close> [50, 0, 0, 0, 50])
  where
    \<open>ss =rr, FF, \<gamma>\<gamma>s\<Rightarrow>\<^sup>* zz' \<equiv> dsteps rr FF \<gamma>\<gamma>s ss zz'\<close>


section \<open> (Strong) Non-interference \<close>

definition
  \<open>rely_obs_safe \<oo> r \<equiv>
    \<forall>hlx hly hsx hsy hs'x hs'y.
      \<bbbA> \<oo> ((hlx,hsx), (hly,hsy)) \<longrightarrow>
      r hsx hs'x \<longrightarrow>
      r hsy hs'y \<longrightarrow>
      \<bbbA> \<oo> ((hlx,hs'x), (hly,hs'y))\<close>

definition                                                                      
  \<open>head_obs_determ \<oo> c \<equiv>
    (\<forall>px qx. (px,qx) \<in> head_atoms c \<longrightarrow>
      (\<forall>py qy. (py,qy) \<in> head_atoms c \<longrightarrow>
        (\<forall>x. px x \<longrightarrow> Ex (qx x) \<longrightarrow>
          (\<forall>y. py y \<longrightarrow> Ex (qy y) \<longrightarrow>
            \<bbbA> \<oo> (x,y) \<longrightarrow>
            px = py \<and> qx = qy))))\<close>

definition                                                                      
  \<open>head_step_obs_safe \<oo> c \<equiv> \<lambda>(x, y).
      \<bbbA> \<oo> (x, y) \<longrightarrow>
        (\<forall>p q x'. (p,q) \<in> head_atoms c \<longrightarrow> p x \<longrightarrow> q x x' \<longrightarrow> \<bbbA> \<oo> (x', y)) \<and>
        (\<forall>p q y'. (p,q) \<in> head_atoms c \<longrightarrow> p y \<longrightarrow> q y y' \<longrightarrow> \<bbbA> \<oo> (x, y')) \<and>
        (\<forall>px qx. (px,qx) \<in> head_atoms c \<longrightarrow>
          (\<forall>py qy. (py,qy) \<in> head_atoms c \<longrightarrow>
          (\<forall>x'. px x \<longrightarrow> qx x x' \<longrightarrow>
          (\<forall>y'. py y \<longrightarrow> qy y y' \<longrightarrow>
            \<bbbA> \<oo> (x',y')))))\<close>


subsection \<open> Determinism \<close>

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


subsubsection \<open> security deterministic endent \<close>

definition
  \<open>sec_head_determ c \<equiv> \<lambda>(sx,sy).
    (\<forall>ca cb. ca \<box> cb \<in> all_subcomm_eq c \<longrightarrow>
      \<not> (heads_dom ca sx \<and> heads_dom cb sy) \<and>
      \<not> (heads_dom cb sx \<and> heads_dom ca sy) \<and>
      \<not> (heads_ccrash_dom ca sx \<and> heads_ccrash_dom cb sy) \<and>
      \<not> (heads_ccrash_dom cb sx \<and> heads_ccrash_dom ca sy))\<close>

lemma sec_head_determ_comm_simps[simp]:
  \<open>sec_head_determ Skip ss = True\<close>
  \<open>sec_head_determ (c1 ;; c2) ss = (sec_head_determ c1 ss \<and> sec_head_determ c2 ss)\<close>
  \<open>sec_head_determ (c1 \<parallel> c2) ss = (sec_head_determ c1 ss \<and> sec_head_determ c2 ss)\<close>
  \<open>sec_head_determ (c1 \<^bold>+ c2) ss = (sec_head_determ c1 ss \<and> sec_head_determ c2 ss)\<close>
  \<open>sec_head_determ (c1 \<box> c2) (sx, sy) =
    (\<not> (heads_dom c1 sx \<and> heads_dom c2 sy) \<and>
      \<not> (heads_dom c2 sx \<and> heads_dom c1 sy) \<and>
      \<not> (heads_ccrash_dom c1 sx \<and> heads_ccrash_dom c2 sy) \<and>
      \<not> (heads_ccrash_dom c2 sx \<and> heads_ccrash_dom c1 sy) \<and>
      sec_head_determ c1 (sx, sy) \<and>
      sec_head_determ c2 (sx, sy))\<close>
  \<open>sec_head_determ \<langle>p, q\<rangle> ss = True\<close>
  \<open>sec_head_determ (DO c OD) (sx, sy) = sec_head_determ c (sx, sy)\<close>
  by (simp add: sec_head_determ_def all_conj_distrib split: prod.splits)+


subsubsection \<open> deterministic steps \<close>

definition                                                                      
  \<open>determ_steps EE r c \<equiv> \<lambda>(x,y).
    EE (exch4 (x,y)) \<longrightarrow>
    (\<forall>\<beta>. vis_pact \<beta> \<longrightarrow>
        (\<forall>x' cx'. (x, c) \<midarrow>\<beta>\<rightarrow>\<^sub>p (Inl x', cx') \<longrightarrow>
          (\<forall>y' cy'. (y, c) \<midarrow>\<beta>\<rightarrow>\<^sub>p (Inl y', cy') \<longrightarrow>
            cx' = cy')))\<close>

lemma determ_steps_apply:
  \<open>determ_steps EE r c (x,y) =
    (EE (exch4 (x,y)) \<longrightarrow>
    (\<forall>\<beta>. vis_pact \<beta> \<longrightarrow>
        (\<forall>x' cx'. (x, c) \<midarrow>\<beta>\<rightarrow>\<^sub>p (Inl x', cx') \<longrightarrow>
          (\<forall>y' cy'. (y, c) \<midarrow>\<beta>\<rightarrow>\<^sub>p (Inl y', cy') \<longrightarrow>
            cx' = cy'))))\<close>
  unfolding determ_steps_def
  by blast

lemma determ_steps_seq_eq[simp]:
  \<open>determ_steps EE r (c1 ;; c2) s = determ_steps EE r c1 s\<close>
  unfolding determ_steps_def
  apply (clarsimp simp add: split_sum_all imp_iff_imp_iff split: prod.splits)
  apply (rule iffI, metis comm.inject(1))
  apply fastforce
  done

lemma determ_steps_commD:
  \<open>determ_steps EE r (c1 ;; c2) s \<Longrightarrow> determ_steps EE r c1 s\<close>
  \<open>determ_steps EE r (c1 \<parallel> c2) s \<Longrightarrow> determ_steps EE r c1 s\<close>
  \<open>determ_steps EE r (c1 \<parallel> c2) s \<Longrightarrow> determ_steps EE r c2 s\<close>
  \<open>determ_steps EE r (c1 \<box> c2) s \<Longrightarrow> determ_steps EE r c1 s\<close>
  \<open>determ_steps EE r (c1 \<box> c2) s \<Longrightarrow> determ_steps EE r c2 s\<close>
  \<open>determ_steps EE r (DO c OD) s \<Longrightarrow> determ_steps EE r c s\<close>
       apply -
       apply (simp; fail)
      apply (clarsimp simp only: determ_steps_def)
      apply (meson comm.inject(2) popstep.simps(5) vis_pact_simps(1); fail)
     apply (clarsimp simp only: determ_steps_def)
     apply (meson comm.inject(2) popstep.simps(5) vis_pact_simps(2); fail)
    apply (clarsimp simp only: determ_steps_def)
    apply (metis not_vis_pact_iff popstep.simps(4))
   apply (clarsimp simp only: determ_steps_def)
   apply (metis not_vis_pact_iff popstep.simps(4))
  apply (clarsimp simp only: determ_steps_def)
  apply (meson comm.inject(1) popstep_then_popstep_doloopD; fail)
  done


section \<open> Noninterference \<close>

definition doubled_atom :: \<open>
    (('l \<times> 'l) \<times> ('s \<times> 's) \<Rightarrow> bool) \<Rightarrow>
    (('l \<times> 'l) \<times> ('s \<times> 's) \<Rightarrow> ('l \<times> 'l) \<times> ('s \<times> 's) \<Rightarrow> bool) \<Rightarrow>
    bool\<close>
  where
    \<open>doubled_atom pp qq \<equiv>
      (\<exists>p. pp = liftP p \<circ> exch4) \<and> (\<exists>q. qq = liftR q \<circ>\<^sub>2 exch4)\<close>

lemma all_doubled_atom_liftC_iff[simp]:
  \<open>all_atom_comm doubled_atom (liftC c)\<close>
  by (induct c)
    (force simp add: doubled_atom_def)+


section \<open> Double step aggregation lemmas \<close>

lemma two_popstep_crash_then_same_post_comm:
  \<open>((sxl, sxs), c) \<midarrow>\<beta>\<rightarrow>\<^sub>p (Inr (), cx') \<Longrightarrow>
    ((syl, sys), c) \<midarrow>\<beta>\<rightarrow>\<^sub>p (Inr (), cy') \<Longrightarrow>
    sec_head_determ c ((sxl, sxs), (syl, sys)) \<Longrightarrow>
    cx' = cy'\<close>
  apply (induct c arbitrary: sxl syl sxs sys cx' cy' \<beta>)
        apply force
       apply force
      apply force
     apply force
    apply (clarsimp simp del: disj_not1 split: if_splits)
     apply (metis Inr_not_Inl popstep_tau_preserves_state split_pairs2)
    apply (elim disjE[of \<open>popstep _ _ _\<close>]) (* 1 \<rightarrow> 4 *)
    (* 1/1 *)
       apply (simp add: vis_tau_pact_incompatible; fail)
    (* 1/2 *)
      apply (frule_tac sc=\<open>((sxl,_),_)\<close> in vis_popstep_impl_atom, assumption)
      apply (frule_tac sc=\<open>((syl,_),_)\<close> in vis_popstep_impl_atom, assumption)
      apply (simp add: heads_ccrash_dom_def vis_tau_pact_incompatible)
      apply (metis ComplI Collect_neg_eq mem_Collect_eq)
    (* 2/1 *)
     apply (frule_tac sc=\<open>((sxl,_),_)\<close> in vis_popstep_impl_atom, assumption)
     apply (frule_tac sc=\<open>((syl,_),_)\<close> in vis_popstep_impl_atom, assumption)
     apply (simp add: heads_ccrash_dom_def vis_tau_pact_incompatible)
     apply (metis ComplI Collect_neg_eq mem_Collect_eq)
    (* 2/2 *)
    apply (simp add: vis_tau_pact_incompatible; fail)
   apply (clarsimp split: if_splits; fail)
  apply force
  done

lemma double_step_crashI:
  \<open>((sxl, sxs), c) \<midarrow>\<beta>\<rightarrow>\<^sub>p (Inr (), c') \<Longrightarrow>
    ((syl, sys), c) \<midarrow>\<beta>\<rightarrow>\<^sub>p (Inr (), c') \<Longrightarrow>
    sec_head_determ c ((sxl, sxs), (syl, sys)) \<Longrightarrow>
    (((sxl, syl), (sxs, sys)), liftC c) \<midarrow>\<beta>\<rightarrow>\<^sub>p (Inr (), liftC c')\<close>
  apply (induct c arbitrary: sxl syl sxs sys c' \<beta>)
        apply force
       apply force
    (* parallel *)
      apply fastforce
    (* indet *)
     apply force
    (* endet *)
    apply (clarsimp split: if_splits)
     apply (metis Inl_Inr_False fst_conv popstep_tau_preserves_state)
    apply (elim disjE) (* 1 \<rightarrow> 4 *)
    (** 1/1 *)
       apply (simp add: vis_tau_pact_incompatible; fail)
    (** 1/2 *)
      apply (frule_tac sc=\<open>((sxl,_),_)\<close> in vis_popstep_impl_atom, assumption)
      apply (frule_tac sc=\<open>((syl,_),_)\<close> in vis_popstep_impl_atom, assumption)
      apply (simp add: heads_ccrash_dom_def vis_tau_pact_incompatible)
      apply (metis ComplI Collect_neg_eq mem_Collect_eq)
    (** 2/1 *)
     apply (frule_tac sc=\<open>((sxl,_),_)\<close> in vis_popstep_impl_atom, assumption)
     apply (frule_tac sc=\<open>((syl,_),_)\<close> in vis_popstep_impl_atom, assumption)
     apply (simp add: heads_ccrash_dom_def vis_tau_pact_incompatible)
     apply (metis ComplI Collect_neg_eq mem_Collect_eq)
    (** 2/2 *)
    apply (simp add: vis_tau_pact_incompatible; fail)
    (* atom *)
   apply (clarsimp split: if_splits; fail)
    (* do-loop *)
  apply clarsimp
  apply (metis two_popstep_crash_then_same_post_comm)
  done

lemma double_no_stepI:
  fixes sxl syl :: \<open>'l::pre_perm_alg\<close>
    and sxs sys :: \<open>'s\<close>
  shows
    \<open>((sxl, sxs), c) \<midarrow>\<sslash>\<rightarrow>\<^sub>p \<Longrightarrow>
    ((syl, sys), c) \<midarrow>\<sslash>\<rightarrow>\<^sub>p \<Longrightarrow>
    (((sxl, syl), (sxs, sys)), liftC c) \<midarrow>\<sslash>\<rightarrow>\<^sub>p\<close>
  apply (induct c arbitrary: sxl syl sxs sys)
    (* Skip *)
        apply force
    (* Seq *)
       apply (clarsimp simp add: liftC_rev_iff, metis)
    (* Parallel *)
      apply simp
      apply (intro allI conjI impI)
        apply (metis liftC_rev_iff(1))
       apply metis
      apply metis
    (* INDet *)
     apply (simp, fast)
    (* ENDet *)
    apply (clarsimp simp add: liftC_rev_iff, metis)
    (* Atom *)
   apply (simp, fastforce)
    (* DoLoop *)
  apply (simp, metis)
  done

lemma double_no_good_stepI:
  fixes sxl syl :: \<open>'l::pre_perm_alg\<close>
    and sxs sys :: \<open>'s\<close>
  shows
    \<open>((sxl, sxs), c) \<midarrow>/\<rightarrow>\<^sub>p \<Longrightarrow>
    ((syl, sys), c) \<midarrow>/\<rightarrow>\<^sub>p \<Longrightarrow>
    (((sxl, syl), (sxs, sys)), liftC c) \<midarrow>/\<rightarrow>\<^sub>p\<close>
  apply (induct c arbitrary: sxl syl sxs sys)
    (* Skip *)
        apply force
    (* Seq *)
       apply (clarsimp simp add: liftC_rev_iff, metis)
    (* Parallel *)
      apply simp
      apply (intro allI conjI impI)
        apply (metis liftC_rev_iff(1))
       apply metis
      apply metis
    (* INDet *)
     apply (simp, fast)
    (* ENDet *)
    apply (clarsimp simp add: liftC_rev_iff, metis)
    (* Atom *)
   apply (simp, fastforce)
    (* DoLoop *)
  apply (simp, metis)
  done

lemma double_no_tau_popstep:
  fixes sxl syl :: \<open>'l::pre_perm_alg\<close>
    and sxs sys :: \<open>'s\<close>
  shows
    \<open>\<forall>s' c'. \<not> ((sxl, sxs), c) \<midarrow>Act Tau\<rightarrow>\<^sub>p (Inl s', c') \<Longrightarrow>
    \<forall>s' c'. \<not> ((syl, sys), c) \<midarrow>Act Tau\<rightarrow>\<^sub>p (Inl s', c') \<Longrightarrow>
    \<forall>s' c'. \<not> (((sxl, syl), (sxs, sys)), liftC c) \<midarrow>Act Tau\<rightarrow>\<^sub>p (Inl s', c')\<close>
  apply (induct c arbitrary: sxl syl sxs sys)
    (* Skip *)
        apply force
    (* Seq *)
       apply (clarsimp simp add: liftC_rev_iff, metis)
    (* Parallel *)
      apply (clarsimp simp add: liftC_rev_iff; fail)
    (* INDet *)
     apply (simp, fast)
    (* ENDet *)
    apply (simp add: liftC_rev_iff, fast)
    (* Atom *)
   apply (simp; fail)
    (* DoLoop *)
  apply (simp, metis)
  done

lemma double_step_endent_tau_helper1:
  shows
    \<open>(\<beta> = Act Tau \<and> c1 = Skip \<and> syl' = syl \<and> sys' = sys \<and> c' = c2 \<or>
      \<beta> = Act Tau \<and> c2 = Skip \<and> syl' = syl \<and> sys' = sys \<and> c' = c1 \<or>
      (\<exists>c1'. c' = c1' \<box> c2 \<and> ((syl, sys), c1) \<midarrow>\<beta>\<rightarrow>\<^sub>p (Inl (syl', sys'), c1')) \<or>
      (\<exists>c2'. c' = c1 \<box> c2' \<and> ((syl, sys), c2) \<midarrow>\<beta>\<rightarrow>\<^sub>p (Inl (syl', sys'), c2'))) \<and>
    (\<beta> = Act Tau \<and> c1 = Skip \<and> sxl' = sxl \<and> sxs' = sxs \<and> c' = c2 \<or>
      \<beta> = Act Tau \<and> c2 = Skip \<and> sxl' = sxl \<and> sxs' = sxs \<and> c' = c1 \<or>
      (\<exists>c1'. c' = c1' \<box> c2 \<and> ((sxl, sxs), c1) \<midarrow>\<beta>\<rightarrow>\<^sub>p (Inl (sxl', sxs'), c1')) \<or>
      (\<exists>c2'. c' = c1 \<box> c2' \<and> ((sxl, sxs), c2) \<midarrow>\<beta>\<rightarrow>\<^sub>p (Inl (sxl', sxs'), c2'))) \<longleftrightarrow>
    (\<exists>c1'. c' = c1' \<box> c2 \<and>
      ((syl, sys), c1) \<midarrow>\<beta>\<rightarrow>\<^sub>p (Inl (syl', sys'), c1') \<and>
      ((sxl, sxs), c1) \<midarrow>\<beta>\<rightarrow>\<^sub>p (Inl (sxl', sxs'), c1')) \<or>
    (\<exists>c2'. c' = c1 \<box> c2' \<and>
      ((syl, sys), c2) \<midarrow>\<beta>\<rightarrow>\<^sub>p (Inl (syl', sys'), c2') \<and>
      ((sxl, sxs), c2) \<midarrow>\<beta>\<rightarrow>\<^sub>p (Inl (sxl', sxs'), c2')) \<or>
    (\<beta> = Act Tau \<and> c1 = Skip \<and> c2 = c' \<or>
      \<beta> = Act Tau \<and> c1 = c' \<and> c2 = Skip) \<and>
      sxl' = sxl \<and> sxs' = sxs \<and> syl' = syl \<and> sys' = sys\<close>
  apply (simp add: conj_disj_distribL conj_disj_distribR)
  apply (rule iffI)
   apply (elim disjE)
                  apply force
                 apply force
                apply force
               apply (metis Pair_inject popstep_endet_skip_then(2))
              apply force
             apply force
            apply (metis Pair_inject popstep_endet_skip_then(1))
           apply force
          apply (metis popstep.simps(1))
         apply (metis Pair_inject popstep_endet_skip_then(1))
        apply force
       apply (clarsimp, metis self_popstep_impossible(1))
      apply (metis Pair_inject popstep_endet_skip_then(2))
     apply (metis popstep.simps(1))
    apply (clarsimp, metis self_popstep_impossible(1))
   apply force
  apply (elim disjE; metis)
  done

lemma double_stepI:
  fixes sxl syl :: \<open>'l::pre_perm_alg\<close>
    and sxs sys :: \<open>'s\<close>
  shows
  \<open>((sxl, sxs), c) \<midarrow>\<beta>\<rightarrow>\<^sub>p (Inl (sxl', sxs'), c') \<Longrightarrow>
    ((syl, sys), c) \<midarrow>\<beta>\<rightarrow>\<^sub>p (Inl (syl', sys'), c') \<Longrightarrow>
    sec_head_determ c ((sxl, sxs), (syl, sys)) \<Longrightarrow>
    (((sxl, syl), (sxs, sys)), liftC c) \<midarrow>\<beta>\<rightarrow>\<^sub>p
      (Inl ((sxl', syl'), (sxs', sys')), liftC c')\<close>
  apply (induct c arbitrary: sxl syl sxs sys sxl' syl' sxs' sys' c' \<beta>)
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
      apply (clarsimp simp add: liftC_rev_iff)
      apply (elim disjE; clarsimp; metis)
      (* INDet *)
     apply fastforce
      (* ENDet *)
    apply (clarsimp del: disjCI split: if_splits simp del: disj_not1)
    (** Tau *)
     apply (simp add: liftC_rev_iff vis_tau_pact_incompatible del: disj_not1)
     apply (drule(1) iffD1[OF double_step_endent_tau_helper1, OF conjI])+
     apply (thin_tac \<open>Not _ \<or> Not _\<close>)+
     apply (thin_tac \<open>_ \<or> _ \<or> _ \<or> _\<close>)+
     apply (elim disjE)
       apply metis
      apply metis
     apply metis
    (** non-Tau *)
    apply (subgoal_tac \<open>\<beta> \<noteq> Act Tau\<close>)
     prefer 2
     apply force
    apply simp
    apply (elim disjE)
    (*** 1/1 *)
       apply (metis not_vis_pact_iff)
    (*** 2/1: forbidden *)
      apply (frule_tac sc=\<open>((sxl,_),_)\<close> in vis_popstep_impl_atom, assumption)
      apply (frule_tac sc=\<open>((syl,_),_)\<close> in vis_popstep_impl_atom, assumption)
      apply (simp add: heads_dom_def)
      apply (metis (mono_tags) inf1I pre_state_def)
    (*** 1/2: forbidden *)
     apply (frule_tac sc=\<open>((sxl,_),_)\<close> in vis_popstep_impl_atom, assumption)
     apply (frule_tac sc=\<open>((syl,_),_)\<close> in vis_popstep_impl_atom, assumption)
     apply (simp add: heads_dom_def)
     apply (metis (mono_tags) inf1I pre_state_def)
    (*** 2/2 *)
    apply (metis not_vis_pact_iff)
    (* Atom *)
   apply (clarsimp split: if_splits; fail)
    (* Do-loop *)
  apply (clarsimp simp add: liftC_rev_iff del: disjCI)
  apply (elim disjE conjE exE)
    (* in order to complete a do-loop, it must be impossible for the sub-program
        to take a step. *)
     apply (simp add: double_no_tau_popstep; fail)
    apply force
   apply force
  apply force
  done


section \<open> Non-interference \<close>

fun etrace_equiv :: \<open>'a eact list \<Rightarrow> 'a eact list \<Rightarrow> bool\<close> where
  \<open>etrace_equiv [] [] = True\<close>
| \<open>etrace_equiv (x # xs) (y # ys) =
    (case (x, y) of
      (Crash \<beta>x, Crash \<beta>y) \<Rightarrow> (\<beta>x = \<beta>y \<and> xs = [] \<and> ys = [])
    | (Loc \<beta>x, Crash \<beta>y) \<Rightarrow> (\<beta>x = \<beta>y \<and> ys = [])
    | (Crash \<beta>x, Loc \<beta>y) \<Rightarrow> (\<beta>x = \<beta>y \<and> xs = [])
    | (x, y) \<Rightarrow> x = y \<and> etrace_equiv xs ys)\<close>
| \<open>etrace_equiv _ _ = False\<close>

lemma etrace_equiv_nil_left_eq[simp]:
  \<open>etrace_equiv [] ys \<longleftrightarrow> ys = []\<close>
  by (induct ys) force+

lemma etrace_equiv_nil_right_eq[simp]:
  \<open>etrace_equiv xs [] \<longleftrightarrow> xs = []\<close>
  by (induct xs) force+

lemma etrace_equiv_crash_left_eq[simp]:
  \<open>etrace_equiv [Crash \<beta>] ys \<longleftrightarrow>
    (\<exists>y ys'. ys = y # ys' \<and> (y = Loc \<beta> \<or> y = Crash \<beta> \<and> ys' = []))\<close>
  by (cases \<open>([Crash \<beta>], ys)\<close> rule: etrace_equiv.cases; simp) (force split: eact.splits)+

lemma etrace_equiv_crash_right_eq[simp]:
  \<open>etrace_equiv xs [Crash \<beta>] \<longleftrightarrow>
    (\<exists>x xs'. xs = x # xs' \<and> (x = Loc \<beta> \<or> x = Crash \<beta> \<and> xs' = []))\<close>
  by (cases \<open>(xs, [Crash \<beta>])\<close> rule: etrace_equiv.cases; simp) (force split: eact.splits)+


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
    \<open>zz = Inl (exch4 (sx, sy))\<close>
    \<open>((sx, c), (sy, c)) =rr, FF, \<gamma>\<gamma>s\<Rightarrow>\<^sup>* ((msx', cx'), (msy', cy'))\<close>
    \<open>length \<gamma>\<gamma>s < n\<close>
    \<open>pred_executions
      (\<lambda>(s, c). (=) s \<^emph>\<and> FF \<le> (sec_head_determ (unliftC c) \<circ> exch4))
      FF rr cc zz n\<close>
  and noninductive_assms:
    \<open>\<forall>l s. FF (l, s) \<longrightarrow> (cancellative \<times>\<^sub>P cancellative) l\<close>
    \<comment> \<open>rely_obs_safe \<oo> r\<close> \<comment> \<open> we don't need this because rr is inherently declassifying \<close>
  shows
    \<open>cx' = cy' \<and> (\<exists>sx' sy'. msx' = Inl sx' \<and> msy' = Inl sy' \<and> SS (exch4 (sx', sy')))\<close>
  using inductive_assms
proof (induct n arbitrary: cc zz c sx sy \<gamma>\<gamma>s cx' cy')
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
    apply (rename_tac sx' c' ly' sy' \<gamma>\<gamma>s' fx fy \<beta>x lx' \<beta>y)
    apply (clarsimp simp add: safe_suc_iff)
    apply (subgoal_tac \<open>\<beta>y = \<beta>x\<close>)
     prefer 2 (* TODO: not true *)
    subgoal sorry
    apply clarsimp
    apply (frule(1) double_stepI[where sxs=sxs and sys=sys])
     apply (clarsimp simp add: pred_executions_suc_iff le_fun_def sepconj_conjI; fail)
    apply (drule_tac x=\<open>strip_pact \<beta>x\<close> in spec, drule spec2, drule spec2,
        drule mp, (rule conjI; assumption))
    apply (drule mp, rule strip_popstep, assumption)
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
     apply (drule mp, rule strip_popstep, assumption)
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

corollary noninterference:
  fixes n :: nat
    and c :: \<open>('l::pre_perm_alg \<times> 's) comm\<close>
    and sx sy :: \<open>'l \<times> 's\<close>
    and r :: \<open>'s \<Rightarrow> 's \<Rightarrow> bool\<close>
    and F :: \<open>'l \<times> 's \<Rightarrow> bool\<close>
  assumes inductive_assms:
    \<open>safe n cc zz rr gg qq SS FF\<close>
    \<open>cc = liftC c\<close>
    \<open>zz = Inl (exch4 (sx, sy))\<close>
    \<open>(sfx, c) \<midarrow>r, \<gamma>s\<rightarrow>\<^sub>e\<^sup>* (Inl sfx', cx')\<close>
    \<open>(sfy, c) \<midarrow>r, \<gamma>s\<rightarrow>\<^sub>e\<^sup>* (Inl sfy', cy')\<close>
    \<open>((=) sx \<^emph>\<and> F) sfx\<close>
    \<open>((=) sy \<^emph>\<and> F) sfy\<close>
    \<open>length \<gamma>s < n\<close>
    \<open>pred_executions
      (\<lambda>(s, c).
        (FF \<midarrow>\<^emph>\<^sub>\<and> (determ_steps (SS \<^emph>\<and> FF) r (unliftC c) \<circ> exch4)) s \<and>
        (FF \<midarrow>\<^emph>\<^sub>\<and> (sec_head_determ (unliftC c) \<circ> exch4)) s)
      FF rr cc zz n\<close>
  and noninductive_assms:
    \<open>\<forall>xl xs. F (xl, xs) \<longrightarrow> cancellative xl\<close>
    \<open>rr = liftR r\<close>
    \<open>FF = liftP F \<circ> exch4\<close>
    \<open>SS = liftP S \<circ> exch4\<close>
    \<open>rely_obs_safe \<oo> r\<close>
    \<open>\<forall>xl xs xs'. r xs xs' \<longrightarrow> F (xl, xs) \<longrightarrow> F (xl, xs')\<close>
    \<open>SS \<^emph>\<and> FF \<le> \<bbbA> \<oo> \<circ> exch4\<close>
  shows
    \<open>(=) (sfx', sfy') \<le> \<bbbA> \<oo>\<close>
  using determ_double_exec_then_safe_state[OF assms(1-15)] assms(16)
  by (clarsimp simp add: sepconj_conj_def exch4_def le_fun_def imp_ex_conjL imp_conjL
      split: prod.splits)


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
  \<open>sc \<midarrow>\<alpha>\<rightarrow> zc' \<Longrightarrow>
    sc = (s, c) \<Longrightarrow>
    zc' = (Inl s', c') \<Longrightarrow>
    all_atoms c' \<le> all_atoms c\<close>
  apply (induct \<alpha> sc zc' arbitrary: s c s' c' rule: opstep.induct)
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
    \<open>z = Inl s\<close>
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

end