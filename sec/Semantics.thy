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


subsection \<open> relational lifting \<close>

definition twoPredLift :: \<open>('a \<Rightarrow> bool) \<Rightarrow> ('b \<Rightarrow> bool) \<Rightarrow> ('a \<times> 'b \<Rightarrow> bool)\<close> where
  \<open>twoPredLift p q \<equiv> \<lambda>(x,y). p x \<and> q y\<close>

nonterminal twoPredLiftL

syntax
  "_twoPredLiftS"  :: "('a \<Rightarrow> bool) \<Rightarrow> twoPredLiftL"  ("\<lblot> _" [0] 1000)
  "_twoPredLiftC"  :: "twoPredLiftL \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool)"  ("_ \<rblot>" [0] 1000)
  "_twoPredLiftL"  :: "twoPredLiftL \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> bool)"  ("_ \<bar>" [0] 1000)
  "_twoPredLiftLR"  :: "twoPredLiftL \<Rightarrow> ('b \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> bool)"  ("_ \<bar> _ \<rblot>" [0] 1000)
  "_twoPredLiftR"  :: "('b \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> bool)"  ("\<bar> _ \<rblot>" [0] 1000)

translations
  "_twoPredLiftC (_twoPredLiftS p)" \<rightharpoonup> "(CONST twoPredLift) p p"
  "_twoPredLiftLR (_twoPredLiftS p) q" \<rightleftharpoons> "(CONST twoPredLift) p q"
  "_twoPredLiftL (_twoPredLiftS p)" \<rightharpoonup> "(CONST twoPredLift) p \<top>"
  "_twoPredLiftR q" \<rightharpoonup> "(CONST twoPredLift) \<top> q"

lemma twoPredLift_apply[simp]:
  \<open>twoPredLift p q (x, y) \<longleftrightarrow> p x \<and> q y\<close>
  by (simp add: twoPredLift_def)

lemma twoPredLiftI[intro]:
  \<open>p x \<Longrightarrow> q y \<Longrightarrow> twoPredLift p q (x, y)\<close>
  by (simp add: twoPredLift_def)

(* FIXME: redundancy *)
lemma \<open>p \<times>\<^sub>P q = \<lblot> p \<bar> q \<rblot>\<close>
  by (simp add: pred_Times_def twoPredLift_def)


subsection \<open> Agreement \<close>

definition sec_agree
  :: \<open>('a \<Rightarrow> 'v) \<Rightarrow> 'a \<times> 'a \<Rightarrow> bool\<close> (\<open>\<bbbA>\<close>)
  where
    \<open>\<bbbA> vf \<equiv> (\<lambda>(x,y). vf x = vf y)\<close>

lemma conj_agree_iff:
  \<open>\<bbbA> v1 \<sqinter> \<bbbA> v2 = \<bbbA> (\<lambda>x. (v1 x, v2 x))\<close>
  by (simp add: sec_agree_def exch4_def comp_def fun_eq_iff split: prod.splits)

subsection \<open> Double-state Lifting \<close>

abbreviation(input) \<open>liftP p \<equiv> \<lblot> p \<rblot>\<close>
definition \<open>liftR r \<equiv> \<lambda>(x,x') (y,y'). r x y \<and> r x' y'\<close>
definition \<open>liftC f \<equiv> map_comm (\<lambda>p q. ((liftP p \<sqinter> \<bbbA> f) \<circ> exch4, liftR q \<circ>\<^sub>2 exch4))\<close>

lemma liftR_apply[simp]:
  \<open>liftR r (x,x') (y,y') \<longleftrightarrow> r x y \<and> r x' y'\<close>
  unfolding liftR_def
  by simp

lemmas liftC_simps[simp] =
  map_comm.simps[of \<open>(\<lambda>p q. ((liftP p \<sqinter> \<bbbA> f) \<circ> exch4, liftR q \<circ>\<^sub>2 exch4))\<close> for f,
    simplified liftC_def[symmetric]]

lemmas liftC_rev_iff =
  map_comm_rev_iff[of \<open>(\<lambda>p q. ((liftP p \<sqinter> \<bbbA> f) \<circ> exch4, liftR q \<circ>\<^sub>2 exch4))\<close> for f,
    simplified liftC_def[symmetric]]

lemma liftC_cancel[simp]:
  \<open>liftC \<oo> ca = liftC \<oo> cb \<longleftrightarrow> ca = cb\<close>
  apply (induct cb arbitrary: ca)
        apply (metis liftC_rev_iff(1))
       apply (metis liftC_rev_iff(2))
      apply (metis liftC_rev_iff(3))
     apply (metis liftC_rev_iff(4))
    apply (metis liftC_rev_iff(5))
   apply (fastforce simp add: liftC_rev_iff fun_eq_iff sec_agree_def liftR_def)
  apply (metis liftC_rev_iff(6))
  done


definition \<open>unliftC \<equiv> map_comm (\<lambda>p q. (\<lambda>x. p (exch4 (x,x)), \<lambda>x y. q (exch4 (x,x)) (exch4 (y,y))))\<close>

lemma unlift_lift_cancel[simp]:
  \<open>unliftC (liftC f c) = c\<close>
  unfolding unliftC_def liftC_def
  by (induct c) (simp add: liftR_def sec_agree_def)+

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


definition \<open>liftC' \<equiv> map_comm (\<lambda>p q. (liftP p \<circ> exch4, liftR q \<circ>\<^sub>2 exch4))\<close>

lemmas liftC'_simps[simp] =
  map_comm.simps[of \<open>(\<lambda>p q. (liftP p \<circ> exch4, liftR q \<circ>\<^sub>2 exch4))\<close> for f,
    simplified liftC'_def[symmetric]]

lemmas liftC'_rev_iff =
  map_comm_rev_iff[of \<open>(\<lambda>p q. (liftP p \<circ> exch4, liftR q \<circ>\<^sub>2 exch4))\<close> for f,
    simplified liftC'_def[symmetric]]

lemma liftC'_cancel[simp]:
  \<open>liftC' ca = liftC' cb \<longleftrightarrow> ca = cb\<close>
  apply (induct cb arbitrary: ca)
        apply (metis liftC'_rev_iff(1))
       apply (metis liftC'_rev_iff(2))
      apply (metis liftC'_rev_iff(3))
     apply (metis liftC'_rev_iff(4))
    apply (metis liftC'_rev_iff(5))
   apply (fastforce simp add: liftC'_rev_iff fun_eq_iff sec_agree_def liftR_def)
  apply (metis liftC'_rev_iff(6))
  done

lemma unlift_lift'_cancel[simp]:
  \<open>unliftC (liftC' c) = c\<close>
  unfolding unliftC_def liftC'_def
  by (induct c) (simp add: liftR_def sec_agree_def)+


section \<open> Tree Noninterference \<close>

section \<open> Safe \<close>

abbreviation tree_weak_noninterference where
  \<open>tree_weak_noninterference \<oo> F \<equiv>
    pred_executions
      (\<lambda>((hl,hs),c).
        (\<forall>hlf. F (hlf,hs) \<longrightarrow> hl ## hlf \<longrightarrow> \<bbbA> \<oo> (exch4 (hl + hlf, hs))) \<and>
        (\<exists>cx. c = liftC' cx))
      F\<close>

lemma opstep_preserves_liftC':
  \<open>(s, liftC' c) \<midarrow>\<alpha>\<rightarrow> (z', cx') \<Longrightarrow> \<exists>c'. cx' = liftC' c'\<close>
proof (induct c arbitrary: s z' cx' \<alpha>)
  case Skip
  then show ?case by force
next
  case (Seq c1 c2)
  then show ?case
    by (simp, metis liftC'_simps(2))
next
  case (Par c1 c2)
  then show ?case
    by (simp, metis liftC'_simps(3))
next
  case (Indet c1 c2)
  then show ?case
    by force
next
  case (Endet c1 c2)
  then show ?case
    using Endet.prems
    by (simp, metis Endet.hyps(2) liftC'_simps(5))
next
  case (Atomic x1 x2)
  then show ?case
    apply (clarsimp split: if_splits)
     apply (metis liftC'_simps(1))
    apply (metis liftC'_rev_iff(7))
    done
next
  case (Iter c)
  then show ?case
    by (clarsimp split: if_splits, metis liftC'_simps(1), metis liftC'_simps(2,7))
qed

lemma opstep_preserves_liftC:
  \<open>(s, liftC \<oo> c) \<midarrow>\<alpha>\<rightarrow> (z', lc') \<Longrightarrow> \<exists>c'. lc' = liftC \<oo> c'\<close>
proof (induct c arbitrary: s \<alpha> z' lc')
  case Skip
  then show ?case
    by simp
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
    by (simp, metis)
next
  case (Endet c1 c2)
  then show ?case
    by (simp, metis liftC_simps(5))
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
    by (simp split: if_splits, metis liftC_simps(1), metis liftC_simps(2,7))
qed

lemma opstep_prestate_liftC'_iff_liftC:
  \<open>\<bbbA> \<oo> (exch4 s) \<Longrightarrow>
    (s, liftC' c) \<midarrow>\<alpha>\<rightarrow> (z', liftC' c') \<longleftrightarrow>
      (s, liftC \<oo> c) \<midarrow>\<alpha>\<rightarrow> (z', liftC \<oo> c')\<close>
proof (induct c arbitrary: s z' \<alpha> c')
  case Skip then show ?case
    by force
next
  case (Seq c1 c2)
  show ?case
    using Seq.prems
    apply (clarsimp simp add: liftC_rev_iff liftC'_rev_iff)
    apply (metis Seq.hyps(1))
    done
next
  case (Par c1 c2)
  show ?case
    using Par.prems
    apply (clarsimp simp add: liftC_rev_iff liftC'_rev_iff)
    apply (metis Par.hyps)
    done
next
  case (Indet c1 c2)
  show ?case
    using Indet.prems
    by (clarsimp simp add: liftC_rev_iff liftC'_rev_iff)
next
  case (Endet c1 c2)
  show ?case
    using Endet.prems
    apply (clarsimp simp add: liftC_rev_iff liftC'_rev_iff)
    apply (metis Endet.hyps(1-2))
    done
next
  case (Atomic x1 x2)
  show ?case 
    using Atomic.prems
    apply (clarsimp simp add: liftC_rev_iff liftC'_rev_iff split: if_splits)
    apply (rule iffI)
     apply clarsimp
    apply clarsimp
    apply (clarsimp simp add: sec_agree_def fun_eq_iff split: prod.splits)
    apply blast
    done
next
  case (Iter c)
  show ?case
    using Iter.prems
    apply (clarsimp simp add: liftC_rev_iff liftC'_rev_iff split: if_splits)
    apply (intro conjI allI impI)
      apply clarsimp
      apply (metis Iter.hyps opstep_preserves_liftC)
     apply clarsimp
     apply (metis Iter.hyps opstep_preserves_liftC')
    apply clarsimp
    apply (metis liftC'_cancel liftC'_simps(7) liftC_cancel liftC_simps(7))
    done
qed

theorem weak_noninterference:
  \<open>safe n c z r g q S F \<Longrightarrow>
    z = Inl s \<Longrightarrow>
    c = liftC' cx \<Longrightarrow>
    S \<^emph>\<and> F \<le> \<bbbA> \<oo> \<circ> exch4 \<Longrightarrow>
    tree_weak_noninterference \<oo> F r c z n\<close>
  apply (induct arbitrary: s cx rule: safe.inducts)
   apply force
  apply (clarsimp simp add: liftC_rev_iff pred_executions_suc_iff)
  apply (rename_tac c hla hlb hsa hsb)
  apply (intro conjI)
   apply (clarsimp simp add: le_fun_def sepconj_conj_def, blast)
  apply clarsimp
  apply (frule opstep_preserves_liftC')
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
abbreviation \<open>pact_tau \<beta> \<equiv> strip_pact \<beta> = Tau\<close>


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
    (if pact_tau \<beta> then
      (\<exists>h' c1'. s' = (h', c1' \<box> c2) \<and> popstep \<beta> (h, c1) (h', c1')) \<or>
      (\<exists>h' c2'. s' = (h', c1 \<box> c2') \<and> popstep \<beta> (h, c2) (h', c2')) \<or>
      c1 = Skip \<and> s' = (Inl h, c2) \<or>
      c2 = Skip \<and> s' = (Inl h, c1)
    else
      popstep \<beta> (h, c1) s' \<or> popstep \<beta> (h, c2) s')\<close>
| \<open>popstep \<beta> (h, c1 \<parallel> c2) s' \<longleftrightarrow>
    \<beta> = Act Tau \<and> c1 = Skip \<and> c2 = Skip \<and> s' = (Inl h, Skip) \<or>
    (\<exists>\<beta>x. \<beta> = PL \<beta>x \<and> (\<exists>h' c1'. popstep \<beta>x (h,c1) (h',c1') \<and> s' = (h', c1' \<parallel> c2))) \<or>
    (\<exists>\<beta>x. \<beta> = PR \<beta>x \<and> (\<exists>h' c2'. popstep \<beta>x (h,c2) (h',c2') \<and> s' = (h', c1 \<parallel> c2')))\<close>
| \<open>popstep \<beta> (h, DO c OD) s' \<longleftrightarrow>
      ((\<forall>h' c'. \<not> popstep \<beta> (h, c) (Inl h', c')) \<longrightarrow>
        \<beta> = Act Tau \<and> s' = (Inl h, Skip)) \<and>
      (\<forall>h' c'.
        popstep \<beta> (h, c) (Inl h', c') \<longrightarrow>
        s' = (Inl h', c' ;; DO c OD)) \<and>
      ((\<exists>c'. popstep \<beta> (h, c) (Inr (), c')) \<longrightarrow>
        s' = (Inr (), DO c OD))\<close>
| \<open>popstep \<beta> (h, Atomic ap aq) s' \<longleftrightarrow>
    (\<exists>a. \<beta> = Act (Vis a) \<and>
          (if ap h
            then \<exists>h'. aq h h' \<and> fst s' = Inl h' \<and> snd s' = Skip
            else fst s' = Inr () \<and> snd s' = Atomic ap aq))\<close>


paragraph \<open> Pretty parallel operational semantics \<close>

abbreviation pretty_popstep :: \<open>_ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> _\<close> (\<open>_ \<midarrow>(_)\<rightarrow>\<^sub>p _\<close> [60,0,60] 60) where
  \<open>hs \<midarrow>\<beta>\<rightarrow>\<^sub>p ht \<equiv> popstep \<beta> hs ht\<close>

abbreviation pretty_no_popstep :: \<open>'s \<times> 's comm \<Rightarrow> bool\<close> (\<open>_ \<midarrow>|\<rightarrow>\<^sub>p\<close> [60] 60) where
  \<open>hs \<midarrow>|\<rightarrow>\<^sub>p \<equiv> \<forall>\<beta> ht. \<not> popstep \<beta> hs ht\<close>


subsubsection \<open> popstep lemmas \<close>

lemma popstep_tau_preserves_heap:
  \<open>sc \<midarrow>\<beta>\<rightarrow>\<^sub>p zc' \<Longrightarrow> pact_tau \<beta> \<Longrightarrow> fst zc' = Inl (fst sc)\<close>
  by (induct rule: popstep.induct)
    (fastforce split: if_splits)+

lemma no_opstep_then_no_popstep:
  \<open>sc \<midarrow>|\<rightarrow> \<Longrightarrow> sc \<midarrow>|\<rightarrow>\<^sub>p\<close>
  apply (induct rule: popstep.induct)
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
  \<open>sc \<midarrow>|\<rightarrow>\<^sub>p \<Longrightarrow> sc \<midarrow>|\<rightarrow>\<close>
  apply (induct rule: popstep.induct)
        apply (clarsimp split: if_splits; fail)
       apply (clarsimp simp add: all_conj_distrib disj_imp split: if_splits; fail)
      apply fastforce
     apply (clarsimp simp add: all_conj_distrib disj_imp split: if_splits)
     apply (case_tac \<open>strip_pact \<beta>\<close>)
      apply (metis act.distinct(1))
     apply (simp, metis act.distinct(1) strip_pact.simps(1))
    apply (clarsimp, metis)
   apply (clarsimp)
  subgoal sorry
  apply force
  done

lemma strip_popstep:
  \<open>sc \<midarrow>\<beta>\<rightarrow>\<^sub>p zc' \<Longrightarrow> sc \<midarrow>strip_pact \<beta>\<rightarrow> zc'\<close>
  apply (induct \<beta> sc zc' rule: popstep.induct)
        apply fastforce
       apply fastforce
      apply fastforce
     apply (clarsimp split: if_splits)
      apply blast
     apply blast
    apply (clarsimp, metis act.distinct(1) strip_pact.simps(1-3))
(*
   apply (force simp add: no_popstep_then_no_opstep split: if_splits)
*)
  subgoal sorry
  apply force
  done

lemma vis_popstep_impl_atom:
  \<open>sc \<midarrow>\<beta>\<rightarrow>\<^sub>p zc' \<Longrightarrow>
    strip_pact \<beta> = Vis a \<Longrightarrow>
    \<exists>p q.
      (p, q) \<in> head_atoms (snd sc) \<and>
      (p (fst sc) \<longrightarrow> (\<exists>s'. fst zc' = Inl s' \<and> q (fst sc) s')) \<and>
      (\<not> p (fst sc) \<longrightarrow> fst zc' = Inr ())\<close>
  by (cases sc, cases zc', clarsimp, metis strip_popstep vis_step_impl_atom)


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

(*
lemma popstep_comm_comm_not_same:
  fixes s :: 's
  assumes \<open>(s, c) \<midarrow>\<beta>\<rightarrow>\<^sub>p (z', c')\<close>
  shows \<open>c' \<noteq> c \<and> c \<notin> endet_cluster c'\<close>
proof -
  { fix sc :: \<open>'s \<times> _\<close> and zc'
    assume \<open>sc \<midarrow>\<beta>\<rightarrow>\<^sub>p zc'\<close>
    then have
      \<open>snd zc' \<noteq> snd sc \<and> snd sc \<notin> endet_cluster (snd zc')\<close>
      apply (induct \<beta> sc zc' rule: popstep.induct)
            apply fastforce
           apply clarsimp
           apply (elim disjE)
            apply (simp, metis in_endet_cluster_then_subcomm
          less_comm_simps_right(2) nless_le)
           apply force
          apply clarsimp
          apply (elim disjE; (simp, metis in_endet_cluster_then_subcomm
            less_comm_simps_right(4) nless_le))
         apply (clarsimp split: if_splits, force)
      sorry
  }
  then show ?thesis
    using assms by force
qed
*)

lemma popstep_comm_not_growing_endet:
  fixes s :: 's
  assumes \<open>(s, c) \<midarrow>\<beta>\<rightarrow>\<^sub>p (z', c')\<close>
  shows \<open>(\<forall>c2. c' \<noteq> c \<box> c2) \<and> (\<forall>c1. c' \<noteq> c1 \<box> c)\<close>
  sorry


subsection \<open> Full step \<close>

definition rel3_merge
  :: \<open>('a \<Rightarrow> 'x \<Rightarrow> 'y \<Rightarrow> bool) \<Rightarrow>
        ('b \<Rightarrow> 'x \<Rightarrow> 'y \<Rightarrow> bool) \<Rightarrow>
        ('a + 'b \<Rightarrow> 'x \<Rightarrow> 'y \<Rightarrow> bool)\<close>
  where
  \<open>rel3_merge u w \<equiv> \<lambda>\<beta>. case \<beta> of Inl \<alpha> \<Rightarrow> u \<alpha> | Inr \<alpha> \<Rightarrow> w \<alpha>\<close>

abbreviation(input) \<open>Env \<equiv> Inl ()\<close>
abbreviation(input) \<open>Loc a \<equiv> Inr a\<close>

definition
  \<open>fstep r F \<equiv>
    rel3_merge
      (\<lambda>() ((hl,hs),c) (h', c').
        c' = c \<and> (\<exists>hs'. h' = Inl (hl, hs') \<and> r hs hs'))
      (\<lambda>\<beta> ((hl,hs), c) (z', c').
        (\<exists>fl.
          F (fl, hs) \<and>
          hl ## fl \<and>
          (case z' of
            Inl (hl', hs') \<Rightarrow>
              F (fl, hs') \<and> hl' ## fl \<and>
              popstep \<beta> ((hl + fl,hs), c) (Inl (hl' + fl,hs'), c')
          | Inr u \<Rightarrow> popstep \<beta> ((hl + fl,hs), c) (Inr u, c'))
        ))\<close>

paragraph \<open> Pretty extended extended opsem \<close>

abbreviation pretty_fstep :: \<open>_ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> _\<close> (\<open>_ \<midarrow>(_, _, _)\<rightarrow>\<^sub>f _\<close> [60,0,0,0,60] 60) where
  \<open>sc \<midarrow>r, F, \<gamma>\<rightarrow>\<^sub>f zc' \<equiv> fstep r F \<gamma> sc zc'\<close>

abbreviation pretty_no_fstep :: \<open>_ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> bool\<close> (\<open>_ \<midarrow>_, _, |\<rightarrow>\<^sub>f\<close> [60, 0, 0] 60) where
  \<open>sc \<midarrow>r, F, |\<rightarrow>\<^sub>f \<equiv> \<forall>\<gamma> zc'. \<not> fstep r F \<gamma> sc zc'\<close>


subsubsection \<open> Lemmas about fstep \<close>

lemma fstep_simps[simp]:
  \<open>fstep r F Env sc zc' =
    (\<exists>hl hs c hs'. sc = ((hl, hs), c) \<and> zc' = (Inl (hl, hs'), c) \<and> r hs hs')\<close>
  \<open>fstep r F (Loc \<beta>) sc zc' =
    (\<exists>hl hs c.
      sc = ((hl,hs), c) \<and>
    (\<exists>z' c'.
      zc' = (z', c') \<and>
      (\<forall>hl' hs'.
        z' = Inl (hl', hs') \<longrightarrow>
        (\<exists>fl.
          F (fl, hs) \<and> hl ## fl \<and>
          F (fl, hs') \<and> hl' ## fl \<and>
          popstep \<beta> ((hl + fl,hs), c) (Inl (hl' + fl,hs'), c'))) \<and>
      (\<forall>u. z' = Inr u \<longrightarrow>
        (\<exists>fl. F (fl, hs) \<and> hl ## fl \<and> popstep \<beta> ((hl + fl,hs), c) (Inr u, c'))
    )))\<close>
   apply (force simp add: fstep_def rel3_merge_def split: sum.splits unit.splits prod.splits)
  apply (clarsimp simp add: fstep_def rel3_merge_def split: sum.splits unit.splits prod.splits)
  apply auto
  done


subsection \<open> Extended step \<close>

definition
  \<open>estep r \<equiv>
    rel3_merge
      (\<lambda>() ((hl,hs),c) (h', c').
        c' = c \<and> (\<exists>hs'. h' = Inl (hl, hs') \<and> r hs hs'))
      popstep\<close>

paragraph \<open> Pretty extended extended opsem \<close>

abbreviation pretty_estep :: \<open>_ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> bool\<close> (\<open>_ \<midarrow>(_, _)\<rightarrow>\<^sub>e _\<close> [60,0,0,60] 60) where
  \<open>sc \<midarrow>r, \<gamma>\<rightarrow>\<^sub>e zc' \<equiv> estep r \<gamma> sc zc'\<close>

abbreviation pretty_no_estep :: \<open>_ \<Rightarrow> _ \<Rightarrow> bool\<close> (\<open>_ \<midarrow>_, |\<rightarrow>\<^sub>e\<close> [60, 0] 60) where
  \<open>sc \<midarrow>r, |\<rightarrow>\<^sub>e \<equiv> \<forall>\<gamma> zc'. \<not> estep r \<gamma> sc zc'\<close>


subsubsection \<open> Lemmas about fstep \<close>

lemma estep_simps[simp]:
  \<open>estep r Env sc zc' =
    (\<exists>hl hs c hs'. sc = ((hl, hs), c) \<and> zc' = (Inl (hl, hs'), c) \<and> r hs hs')\<close>
  \<open>estep r (Loc \<beta>) sc zc' = popstep \<beta> sc zc'\<close>
  by (force simp add: estep_def rel3_merge_def split: sum.splits unit.splits prod.splits)+


section \<open> Trace Semantics \<close>

paragraph \<open> Pretty extended operational semantics \<close>

text \<open>
  NOTE: the most recent action is at the *end* of the list
\<close>
inductive fsteps
  :: \<open>('s \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow>
      ('l::pre_perm_alg \<times> 's \<Rightarrow> bool) \<Rightarrow>
      _ list \<Rightarrow>
      ('l \<times> 's) pconfig \<Rightarrow>
      ('l \<times> 's) cpconfig \<Rightarrow>
      bool\<close>
  where
  epopsteps_nil[intro!]: \<open>zc' = (Inl (fst sc), snd sc) \<Longrightarrow> fsteps r F [] sc zc'\<close>
| epopsteps_step[intro!]:
    \<open>fstep r F \<alpha> sc (Inl s', c') \<Longrightarrow>
      fsteps r F \<alpha>s (s', c') zc'' \<Longrightarrow>
      fsteps r F (\<alpha>#\<alpha>s) sc zc''\<close>

inductive_cases fsteps_nil[elim!]: \<open>fsteps r F [] sc zc'\<close>
inductive_cases fsteps_step[elim!]: \<open>fsteps r F (\<alpha> # \<alpha>s) sc zc'\<close>

abbreviation pretty_fsteps (\<open>_ \<midarrow>(_, _, _)\<rightarrow>\<^sub>f\<^sup>* _\<close> [60,0,0,0,60] 60) where
  \<open>hs \<midarrow>r, F, \<alpha>s\<rightarrow>\<^sub>f\<^sup>* ht \<equiv> fsteps r F \<alpha>s hs ht\<close>

(*
subsection \<open> Alignment \<close>

fun pact_aligned :: \<open>'a pact \<Rightarrow> 'a pact \<Rightarrow> bool\<close> where
  \<open>pact_aligned (PL \<beta>x) (PL \<beta>y) \<longleftrightarrow> pact_aligned \<beta>x \<beta>y\<close>
| \<open>pact_aligned (PR \<beta>x) (PR \<beta>y) \<longleftrightarrow> pact_aligned \<beta>x \<beta>y\<close>
| \<open>pact_aligned (Act \<alpha>x) (Act \<alpha>y) \<longleftrightarrow> \<alpha>x = \<alpha>y\<close>
| \<open>pact_aligned _ _ \<longleftrightarrow> False\<close>

lemma
  \<open>pact_aligned \<beta>x \<beta>y \<longleftrightarrow> \<beta>x = \<beta>y\<close>
  apply (induct \<beta>x \<beta>y rule: pact_aligned.induct)
            apply force+
  done

lemma pact_merge_rev_act:
  \<open>pact_aligned \<beta>x \<beta>y \<Longrightarrow>
    pact_merge \<beta>x \<beta>y = Act \<alpha> \<longleftrightarrow> \<beta>x = Act \<alpha> \<and> \<beta>y = Act \<alpha>\<close>
  by (induct \<beta>x \<beta>y arbitrary: \<alpha> rule: pact_aligned.induct) force+

lemma pact_merge_rev_pl:
  \<open>pact_aligned \<beta>x \<beta>y \<Longrightarrow>
    pact_merge \<beta>x \<beta>y = PL \<beta>' \<longleftrightarrow>
      (\<exists>\<beta>x' \<beta>y'. \<beta>x = PL \<beta>x' \<and> \<beta>y = PL \<beta>y' \<and> pact_merge \<beta>x' \<beta>y' = \<beta>')\<close>
  by (induct \<beta>x \<beta>y arbitrary: \<beta>' rule: pact_aligned.induct) force+

lemma pact_merge_rev_pr:
  \<open>pact_aligned \<beta>x \<beta>y \<Longrightarrow>
    pact_merge \<beta>x \<beta>y = PR \<beta>' \<longleftrightarrow>
      (\<exists>\<beta>x' \<beta>y'. \<beta>x = PR \<beta>x' \<and> \<beta>y = PR \<beta>y' \<and> pact_merge \<beta>x' \<beta>y' = \<beta>')\<close>
  by (induct \<beta>x \<beta>y arbitrary: \<beta>' rule: pact_aligned.induct) force+

lemma pact_merge_taus_is_tau:
  \<open>pact_aligned \<beta>x \<beta>y \<Longrightarrow>
    pact_tau \<beta>x \<Longrightarrow>
    pact_tau \<beta>y \<Longrightarrow>
    pact_tau (pact_merge \<beta>x \<beta>y)\<close>
  by (induct \<beta>x \<beta>y rule: pact_aligned.induct) force+

lemmas pact_merge_rev =
  pact_merge_rev_act pact_merge_rev_pl pact_merge_rev_pr


fun fact_aligned :: \<open>unit + 'a pact \<Rightarrow> unit + 'a pact \<Rightarrow> bool\<close> where
  \<open>fact_aligned Env Env \<longleftrightarrow> True\<close>
| \<open>fact_aligned (Loc \<beta>x) (Loc \<beta>y) \<longleftrightarrow> pact_aligned \<beta>x \<beta>y\<close>
| \<open>fact_aligned _ _ \<longleftrightarrow> False\<close>

lemma fact_aligned_iff:
  \<open>fact_aligned \<gamma>x \<gamma>y \<longleftrightarrow>
    \<gamma>x = Env \<and> \<gamma>y = Env \<or>
    (\<exists>\<beta>x \<beta>y. \<gamma>x = Loc \<beta>x \<and> \<gamma>y = Loc \<beta>y \<and> pact_aligned \<beta>x \<beta>y)\<close>
  by (meson fact_aligned.elims(2) fact_aligned.simps(1-2))

abbreviation \<open>parallel_aligned \<equiv> list_all2 fact_aligned\<close>
*)


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
  \<open>sec_determ_endet c \<equiv> \<lambda>(sx,sy).
    (\<forall>ca cb. ca \<box> cb \<in> all_subcomm_eq c \<longrightarrow>
      \<not> (heads_dom ca sx \<and> heads_dom cb sy) \<and>
      \<not> (heads_dom cb sx \<and> heads_dom ca sy) \<and>
      \<not> (heads_ccrash_dom ca sx \<and> heads_ccrash_dom cb sy) \<and>
      \<not> (heads_ccrash_dom cb sx \<and> heads_ccrash_dom ca sy))\<close>

lemma sec_determ_endet_comm_simps[simp]:
  \<open>sec_determ_endet Skip ss = True\<close>
  \<open>sec_determ_endet (c1 ;; c2) ss = (sec_determ_endet c1 ss \<and> sec_determ_endet c2 ss)\<close>
  \<open>sec_determ_endet (c1 \<parallel> c2) ss = (sec_determ_endet c1 ss \<and> sec_determ_endet c2 ss)\<close>
  \<open>sec_determ_endet (c1 \<^bold>+ c2) ss = (sec_determ_endet c1 ss \<and> sec_determ_endet c2 ss)\<close>
  \<open>sec_determ_endet (c1 \<box> c2) (sx, sy) =
    (\<not> (heads_dom c1 sx \<and> heads_dom c2 sy) \<and>
      \<not> (heads_dom c2 sx \<and> heads_dom c1 sy) \<and>
      \<not> (heads_ccrash_dom c1 sx \<and> heads_ccrash_dom c2 sy) \<and>
      \<not> (heads_ccrash_dom c2 sx \<and> heads_ccrash_dom c1 sy) \<and>
      sec_determ_endet c1 (sx, sy) \<and>
      sec_determ_endet c2 (sx, sy))\<close>
  \<open>sec_determ_endet \<langle>p, q\<rangle> ss = True\<close>
  \<open>sec_determ_endet (DO c OD) ss = sec_determ_endet c ss\<close>
  by (simp add: sec_determ_endet_def all_conj_distrib ball_Un split: prod.splits)+


subsubsection \<open> deterministic steps \<close>

definition                                                                      
  \<open>determ_steps \<oo> r F c \<equiv> \<lambda>(x,y).
    \<bbbA> \<oo> (x,y) \<longrightarrow>
    (\<forall>\<gamma> x' cx'.
      (x, c) \<midarrow>r, F, \<gamma>\<rightarrow>\<^sub>f (Inl x', cx') \<longrightarrow>
      (\<forall>y' cy'.
        (y, c) \<midarrow>r, F, \<gamma>\<rightarrow>\<^sub>f (Inl y', cy') \<longrightarrow>
        cx' = cy' \<and> \<bbbA> \<oo> (x',y')))\<close>

lemma determ_steps_simps[simp]:
  \<open>(\<forall>slx ssx sly ssy. \<forall>ssx' ssy'.
      s = ((slx, ssx), (sly, ssy)) \<longrightarrow>
      \<bbbA> \<oo> ((slx, ssx), (sly, ssy)) \<longrightarrow>
      r ssx ssx' \<longrightarrow>
      r ssy ssy' \<longrightarrow>
      \<bbbA> \<oo> ((slx, ssx'), (sly, ssy'))
    ) \<Longrightarrow> determ_steps \<oo> r F Skip s = True\<close>
  \<open>determ_steps \<oo> r F (c1 ;; c2) s = determ_steps \<oo> r F c1 s\<close>
  \<open>determ_steps \<oo> r F \<langle>p, q\<rangle> s = True\<close>
(*
  \<open>determ_steps \<oo> r F (c1 \<^bold>+ c2) s = X\<close>
  \<open>determ_steps \<oo> r F (c1 \<box> c2) s = X\<close>
  \<open>determ_steps \<oo> r F (c1 \<parallel> c2) s = X\<close>
  \<open>determ_steps \<oo> r F (DO c OD) s = X\<close>
*)
  unfolding determ_steps_def
    apply -
    apply (clarsimp simp add: split_sum_all; fail)
   apply (clarsimp simp add: split_sum_all imp_iff_imp_iff split: prod.splits)
   apply (intro iffI)
    apply (metis comm.inject(1))
   apply clarsimp
   apply (elim disjE)
  oops

lemma determ_steps_commD:
  \<open>determ_steps \<oo> r F (c1 ;; c2) s \<Longrightarrow> determ_steps \<oo> r F c1 s\<close>
  \<open>determ_steps \<oo> r F (c1 \<parallel> c2) s \<Longrightarrow> determ_steps \<oo> r F c1 s\<close>
  \<open>determ_steps \<oo> r F (c1 \<parallel> c2) s \<Longrightarrow> determ_steps \<oo> r F c2 s\<close>
  \<open>determ_steps \<oo> r F (c1 \<box> c2) s \<Longrightarrow> determ_steps \<oo> r F c1 s\<close>
  \<open>determ_steps \<oo> r F (c1 \<box> c2) s \<Longrightarrow> determ_steps \<oo> r F c2 s\<close>
  \<open>determ_steps \<oo> r F (DO c OD) s \<Longrightarrow> determ_steps \<oo> r F c s\<close>
  sorry

(*
lemma determ_stepsD:
  \<open>determ_steps \<oo> r F c (x,y) \<Longrightarrow>
    (x, c) \<midarrow>r, F, \<alpha>x\<rightarrow>\<^sub>f (Inl x', cx') \<Longrightarrow>
    (y, c) \<midarrow>r, F, \<alpha>y\<rightarrow>\<^sub>f (Inl y', cy') \<Longrightarrow>
    \<bbbA> \<oo> (x, y) \<Longrightarrow>
    cx' = cy' \<and> \<bbbA> \<oo> (x', y')\<close>
  unfolding determ_steps_def
  by (simp, metis surj_pair)
*)

lemma determ_pstepD:
  \<open>determ_steps \<oo> r F c (x,y) \<Longrightarrow>
    (x, c) \<midarrow>\<beta>\<rightarrow>\<^sub>p (Inl x', cx') \<Longrightarrow>
    (y, c) \<midarrow>\<beta>\<rightarrow>\<^sub>p (Inl y', cy') \<Longrightarrow>
    \<bbbA> \<oo> (x, y) \<Longrightarrow>
    cx' = cy' \<and> \<bbbA> \<oo> (x', y')\<close>
  unfolding determ_steps_def
  apply clarsimp
  oops


subsection \<open> Separation Respecting Agreement \<close>

definition sec_sepsafe_agree
  :: \<open>(_ \<Rightarrow> 'v) \<Rightarrow>('a::pre_perm_alg \<times> 'b) \<times> ('a \<times> 'b) \<Rightarrow> bool\<close> (\<open>\<bbbS>\<close>)
  where
    \<open>\<bbbS> \<oo> \<equiv> \<lambda>(x,y).
      \<forall>x' y'. x' \<preceq> fst x \<longrightarrow> y' \<preceq> fst y \<longrightarrow> sepdomeq x' y' \<longrightarrow> \<oo> (x', snd x) = \<oo> (y', snd y)\<close>

lemma sec_sepsafe_agree_conj:
  \<open>\<bbbS> f \<sqinter> \<bbbS> g = \<bbbS> (\<lambda>x. (f x, g x))\<close>
  unfolding sec_sepsafe_agree_def
  by blast


section \<open> Noninterference \<close>

lemma noninterference_step:
  fixes n :: nat
    and c :: \<open>('l::pre_perm_alg \<times> 's) comm\<close>
    and sx sy :: \<open>'l \<times> 's\<close>
    and r :: \<open>'s \<Rightarrow> 's \<Rightarrow> bool\<close>
    and \<oo> :: \<open>'l \<times> 's \<Rightarrow> 'v\<close>
  shows
  \<open>(sx, c) \<midarrow>r, \<gamma>\<rightarrow>\<^sub>e (Inl sx', cx') \<Longrightarrow>
    (sy, c) \<midarrow>r, \<gamma>\<rightarrow>\<^sub>e (Inl sy', cy') \<Longrightarrow>
    rely_obs_safe \<oo> r \<Longrightarrow>
    head_step_obs_safe \<oo> c (sx, sy) \<Longrightarrow>
    determ_steps \<oo> r F c (sx, sy) \<Longrightarrow>
    \<forall>xl xs. F (xl, xs) \<longrightarrow> cancellative xl \<Longrightarrow>
    \<bbbA> \<oo> (sx, sy) \<Longrightarrow>
    \<bbbA> \<oo> (sx', sy')\<close>
  apply (clarsimp simp del: comp_apply)
  apply (case_tac \<gamma>)
   apply (clarsimp simp del: comp_apply simp add: rely_obs_safe_def)
   apply (drule spec2[of _ \<open>fst sx\<close> \<open>fst sy\<close>], drule spec2[of _ \<open>snd sx\<close> \<open>snd sy\<close>])
   apply force
  apply clarsimp
  apply (frule strip_popstep[of _ _ \<open>(z', cx')\<close> for z'])
  apply (frule strip_popstep[of _ _ \<open>(z', cy')\<close> for z'])
  sorry

lemma fstep_preserves_safe:
  \<open>\<forall>f. F (f, hs) \<longrightarrow> hl ## f \<longrightarrow>
      F (f, hs') \<longrightarrow> hl' ## f \<longrightarrow>
      ((hl + f, hs), c) \<midarrow>r, \<beta>\<rightarrow>\<^sub>e (Inl (hl' + f, hs'), c') \<Longrightarrow>
    \<forall>f. F (f, hs) \<longrightarrow> F (f, hs') \<longrightarrow> cancellative f \<Longrightarrow>
    \<exists>f. F (f, hs) \<and> hl ## f \<and> F (f, hs') \<and> hl' ## f \<Longrightarrow>
    safe (Suc n) c (Inl (hl, hs)) r g q S F \<Longrightarrow>
    safe n c' (Inl (hl', hs')) r g q S F\<close>
  apply (cases n)
   apply (force simp add: safe_suc_iff fstep_def rel3_merge_def split: sum.splits unit.splits)
  apply (clarsimp simp add: safe_suc_iff estep_def rel3_merge_def split: sum.splits unit.splits)
    (* rely step *)
   apply (intro conjI; metis cancellative_def)
    (* opstep step *)
  apply (intro conjI)
     apply (metis Inl_inject Pair_inject cancellative_def strip_popstep)
    apply (metis Inl_inject Pair_inject cancellative_def strip_popstep)
   apply (metis Inl_inject Pair_inject cancellative_def strip_popstep)
  apply (drule spec, drule mp, assumption, drule mp, assumption,
      drule mp, assumption, drule mp, assumption,
      frule strip_popstep)
  apply clarsimp
  apply (drule spec, drule mp, assumption, drule mp, assumption)
  apply (drule spec, drule mp, assumption)
  apply (drule spec2, drule spec, drule mp, assumption, drule mp, assumption)
  apply clarsimp
  apply (metis cancellative_def)
  done

(*
lemma pact_aligned_then_strip_pact_eq:
  \<open>pact_aligned \<beta>x \<beta>y \<Longrightarrow> strip_pact \<beta>y = strip_pact \<beta>x\<close>
  by (induct \<beta>x \<beta>y rule: pact_aligned.induct) force+

lemma pact_aligned_strip_pact_merge_eq[simp]:
  \<open>pact_aligned \<beta>x \<beta>y \<Longrightarrow> strip_pact (pact_merge \<beta>x \<beta>y) = strip_pact \<beta>x\<close>
  by (induct \<beta>x \<beta>y rule: pact_aligned.induct) force+
*)

definition doubled_atom :: \<open>
    (('l \<times> 'l) \<times> ('s \<times> 's) \<Rightarrow> bool) \<Rightarrow>
    (('l \<times> 'l) \<times> ('s \<times> 's) \<Rightarrow> ('l \<times> 'l) \<times> ('s \<times> 's) \<Rightarrow> bool) \<Rightarrow>
    bool\<close>
  where
    \<open>doubled_atom pp qq \<equiv>
      (\<exists>p. pp = liftP p \<circ> exch4) \<and> (\<exists>q. qq = liftR q \<circ>\<^sub>2 exch4)\<close>

lemma double_step_fstD:
  fixes ss :: \<open>('l \<times> 'l) \<times> ('s \<times> 's)\<close>
    and cc :: \<open>(('l \<times> 'l) \<times> ('s \<times> 's)) comm\<close>
  shows
  \<open>(ss, cc) \<midarrow>\<beta>\<rightarrow>\<^sub>p (zz', cc') \<Longrightarrow>
    all_atom_comm doubled_atom cc \<Longrightarrow>
    case zz' of
      Inl ss' \<Rightarrow>
        (fst (exch4 ss), unliftC cc) \<midarrow>\<beta>\<rightarrow>\<^sub>p (Inl (fst (exch4 ss')), unliftC cc')
    | Inr () \<Rightarrow> (fst (exch4 ss), unliftC cc) \<midarrow>\<beta>\<rightarrow>\<^sub>p (Inr (), unliftC cc')\<close>
  apply (induct cc arbitrary: \<beta> cc' ss zz')
        apply force
       apply (case_tac zz')
        apply clarsimp
        apply (erule disjE, force)
        apply clarsimp
        apply fastforce
       apply (clarsimp split: unit.splits)
       apply (metis fst_conv sum.simps(6) old.unit.case prod_part_destruct_exch4_eq(1))
      apply (clarsimp split: sum.splits unit.splits del: disjCI)
      apply (rule conjI)
       apply (clarsimp del: disjCI)
  sorry
(*
   apply (cases ss, force simp add: unliftC_rev_iff doubled_atom_def
      split: if_splits)
*)

lemma double_step_sndD:
  \<open>(ss, cc) \<midarrow>\<beta>\<rightarrow>\<^sub>p (zz', cc') \<Longrightarrow>
    all_atom_comm doubled_atom cc \<Longrightarrow>
    case zz' of
      Inl ss' \<Rightarrow>
        (snd (exch4 ss), unliftC cc) \<midarrow>\<beta>\<rightarrow>\<^sub>p (Inl (snd (exch4 ss')), unliftC cc')
    | Inr () \<Rightarrow> (snd (exch4 ss), unliftC cc) \<midarrow>\<beta>\<rightarrow>\<^sub>p (Inr (), unliftC cc')\<close>
  sorry

lemma all_doubled_atom_liftC'_iff[simp]:
  \<open>all_atom_comm doubled_atom (liftC' c)\<close>
  sorry

lemma double_step_crashI:
  \<open>((sxl, sxs), c) \<midarrow>\<beta>\<rightarrow>\<^sub>p (Inr (), c') \<Longrightarrow>
    ((syl, sys), c) \<midarrow>\<beta>\<rightarrow>\<^sub>p (Inr (), c') \<Longrightarrow>
    sec_determ_endet c ((sxl, sxs), (syl, sys)) \<Longrightarrow>
    (((sxl, syl), (sxs, sys)), liftC' c) \<midarrow>\<beta>\<rightarrow>\<^sub>p (Inr (), liftC' c')\<close>
  apply (induct c arbitrary: sxl syl sxs sys c' \<beta>)
        apply force
       apply force
    (* parallel *)
      apply clarsimp
  subgoal sorry
      (* indet *)
     apply force
    (* endet *)
    apply (clarsimp split: if_splits)
     apply (metis Inl_not_Inr fst_eqD popstep_tau_preserves_heap)
    apply (elim disjE) (* 1 \<rightarrow> 4 *)
    (** 1/1 *)
       apply blast
    (** 1/2 *)
      apply (frule_tac sc=\<open>((sxl,_),_)\<close> in vis_popstep_impl_atom, assumption)
      apply (frule_tac sc=\<open>((syl,_),_)\<close> in vis_popstep_impl_atom, assumption)
      apply (simp add: heads_ccrash_dom_def)
      apply (metis ComplI Collect_neg_eq mem_Collect_eq)
    (** 2/1 *)
     apply (frule_tac sc=\<open>((sxl,_),_)\<close> in vis_popstep_impl_atom, assumption)
     apply (frule_tac sc=\<open>((syl,_),_)\<close> in vis_popstep_impl_atom, assumption)
     apply (simp add: heads_ccrash_dom_def)
     apply (metis ComplI Collect_neg_eq mem_Collect_eq)
    (** 2/2 *)
    apply blast
    (* atom *)
   apply (clarsimp split: if_splits; fail)
    (* do-loop *)
  apply force
  done

lemma double_stepI:
  fixes sxl syl :: \<open>'l::pre_perm_alg\<close>
    and sxs sys :: \<open>'s\<close>
  shows
  \<open>((sxl, sxs), c) \<midarrow>\<beta>\<rightarrow>\<^sub>p (Inl (sxl', sxs'), c') \<Longrightarrow>
    ((syl, sys), c) \<midarrow>\<beta>\<rightarrow>\<^sub>p (Inl (syl', sys'), c') \<Longrightarrow>
    determ_steps \<oo> r F c ((sxl, sxs), (syl, sys)) \<Longrightarrow>
    sec_determ_endet c ((sxl, sxs), (syl, sys)) \<Longrightarrow>
    \<nexists>c'. ((sxl, sxs), c) \<midarrow>\<beta>\<rightarrow>\<^sub>p (Inr (), c') \<Longrightarrow>
    \<nexists>c'. ((syl, sys), c) \<midarrow>\<beta>\<rightarrow>\<^sub>p (Inr (), c') \<Longrightarrow>
    (((sxl, syl), (sxs, sys)), liftC' c)
      \<midarrow>\<beta>\<rightarrow>\<^sub>p
      (Inl ((sxl', syl'), (sxs', sys')), liftC' c')\<close>
  apply (induct c arbitrary: sxl syl sxs sys sxl' syl' sxs' sys' c' \<beta>)
    (* Skip *)
        apply force
    (* Seq *)
       apply clarsimp
       apply (elim disjE)
          apply force
         apply force
        apply force
       apply clarsimp
       apply (metis determ_steps_commD(1))
    (* Parallel *)
      apply (clarsimp simp add: liftC'_rev_iff)
      apply (elim disjE)
              apply force
             apply force
            apply force
           apply force
          apply force
         apply clarsimp
  subgoal sorry
        apply fastforce
       apply fastforce
      apply clarsimp
  subgoal sorry
      (* INDet *)
     apply fastforce
      (* ENDet *)
    apply (clarsimp del: disjCI split: if_splits)
    (** Tau *)
     apply (subgoal_tac
      \<open>c1 = Skip \<and> c2 = Skip \<and> c' = Skip \<or>
        c1 = Skip \<and> c2 \<noteq> Skip \<and> c' = c2 \<or>
        c1 \<noteq> Skip \<and> c2 = Skip \<and> c' = c1 \<or>
        (\<exists>c1'. c' = c1' \<box> c2) \<or>
        (\<exists>c2'. c' = c1 \<box> c2')\<close>)
      prefer 2
      apply (clarsimp, metis)
  subgoal sorry
      (** non-Tau *)
    apply (elim disjE) (* +3 *)
    (*** 1/1 *)
       apply (metis determ_steps_commD(4))
    (*** 2/1 *)
      apply (frule_tac sc=\<open>((sxl,_),_)\<close> in vis_popstep_impl_atom, assumption)
      apply (frule_tac sc=\<open>((syl,_),_)\<close> in vis_popstep_impl_atom, assumption)
      apply (simp add: heads_dom_def)
      apply (metis (mono_tags) inf1I pre_state_def)
    (*** 1/2 *)
     apply (frule_tac sc=\<open>((sxl,_),_)\<close> in vis_popstep_impl_atom, assumption)
     apply (frule_tac sc=\<open>((syl,_),_)\<close> in vis_popstep_impl_atom, assumption)
     apply (simp add: heads_dom_def)
     apply (metis (mono_tags) inf1I pre_state_def)
    (*** 2/2 *)
    apply (metis determ_steps_commD(5))
    (* Atom *)
   apply (clarsimp split: if_splits; fail)
    (* Do-loop *)
  apply clarsimp
  apply (case_tac \<open>(\<forall>a b c'. \<not> ((sxl, sxs), c) \<midarrow>\<beta>\<rightarrow>\<^sub>p (Inl (a, b), c'))\<close>)
   apply clarsimp
    \<comment> \<open> CASE: complete deadlock
          PROBLEM: we need to be able to combine the negative steps too. \<close>
  subgoal sorry
  apply clarsimp
  apply (subgoal_tac \<open>determ_steps \<oo> r F c ((sxl, sxs), syl, sys)\<close>)
   prefer 2
   apply (metis determ_steps_commD(6))
  apply (rename_tac sxl'' sxs'' cx'' syl'' sys'' cy'')
  apply (subgoal_tac \<open>(((sxl, syl), sxs, sys), liftC' c) \<midarrow>\<beta>\<rightarrow>\<^sub>p (Inl ((sxl'', syl''), sxs'', sys''), liftC' cy'')\<close>)
   prefer 2
   apply blast
  apply (intro conjI)
    apply blast
   prefer 2
   apply clarsimp
   apply (frule double_step_fstD, (simp; fail))
   apply (clarsimp split: unit.splits; fail)
  apply clarsimp
  apply (frule double_step_fstD, (simp; fail))
  apply (frule double_step_sndD, (simp; fail))
  apply (clarsimp split: unit.splits)
  apply (metis opstep_preserves_liftC' strip_popstep unlift_lift'_cancel)
  done

theorem double_determ_exec_then_safe_state:
  fixes n :: nat
    and c :: \<open>('l::pre_perm_alg \<times> 's) comm\<close>
    and sx sy :: \<open>'l \<times> 's\<close>
    and r :: \<open>'s \<Rightarrow> 's \<Rightarrow> bool\<close>
    and F :: \<open>'l \<times> 's \<Rightarrow> bool\<close>
  shows
  \<open>safe n cc zz rr gg qq SS FF \<Longrightarrow>
    cc = liftC' c \<Longrightarrow>
    zz = Inl (exch4 (sx, sy)) \<Longrightarrow>
    rr = liftR r \<Longrightarrow>
    FF = liftP F \<circ> exch4 \<Longrightarrow>
    (sx, c) \<midarrow>r, F, \<gamma>s\<rightarrow>\<^sub>f\<^sup>* (Inl sx', cx') \<Longrightarrow>
    (sy, c) \<midarrow>r, F, \<gamma>s\<rightarrow>\<^sub>f\<^sup>* (Inl sy', cy') \<Longrightarrow>
    length \<gamma>s < n \<Longrightarrow>
    pred_executions
      (\<lambda>(s,c).
        determ_steps \<oo> r F (unliftC c) (exch4 s) \<and>
        sec_determ_endet (unliftC c) (exch4 s))
      FF rr cc zz n \<Longrightarrow>
    \<forall>xl xs. F (xl, xs) \<longrightarrow> cancellative xl \<Longrightarrow>
    rely_obs_safe \<oo> r \<Longrightarrow>
    SS (exch4 (sx', sy'))\<close>
proof (induct n arbitrary: cc zz c sx sy \<gamma>s sx' sy')
  case 0
  then show ?case
    by (clarsimp simp add: le_fun_def)
next
  case (Suc n)

  have state_pred: \<open>\<forall>ss. zz = Inl ss \<longrightarrow> SS ss\<close>
    using Suc.prems(1)
    by (clarsimp simp add: safe_suc_iff)

  obtain sxl sxs where sx_split: \<open>sx = (sxl, sxs)\<close>
    by fastforce
  obtain syl sys where sy_split: \<open>sy = (syl, sys)\<close>
    by fastforce

  have safe_suc_conseq:
    \<open>cc = Skip \<longrightarrow> qq ((sxl, syl), (sxs, sys))\<close>
    \<open>SS ((sxl, syl), (sxs, sys))\<close>
    \<open>\<And>hs'. rr (sxs, sys) hs' \<Longrightarrow> safe n cc (Inl ((sxl, syl), hs')) rr gg qq SS FF\<close>
    \<open>\<And>\<alpha> z' c' fx fy.
      (((sxl + fx, syl + fy), (sxs, sys)), liftC' c) \<midarrow>\<alpha>\<rightarrow> (z', c') \<Longrightarrow>
      sxl ## fx \<Longrightarrow>
      syl ## fy \<Longrightarrow>
      F (fx, sxs) \<Longrightarrow>
      F (fy, sys) \<Longrightarrow>
      (\<exists>hlx' hly' hs'.
        hlx' ## fx \<and>
        hly' ## fy \<and>
        z' = Inl ((hlx' + fx, hly' + fy), hs') \<and>
        (\<alpha> \<noteq> Tau \<longrightarrow> gg (sxs, sys) hs') \<and>
        (\<alpha> = Tau \<longrightarrow> hlx' = sxl \<and> hly' = syl) \<and>
        safe n c' (Inl ((hlx', hly'), hs')) rr gg qq SS FF)\<close>
    using Suc.prems(1-3,5) sx_split sy_split
       apply -
       apply (simp add: safe_suc_iff)+
     apply force
    apply (clarsimp simp add: safe_suc_iff, metis)
    done

  show ?case
    using Suc.prems(2-3,6-) safe_suc_conseq(1,2) sx_split sy_split
    apply (clarsimp simp add: liftC'_rev_iff simp del: comp_apply)
    apply (erule fsteps.cases, force)
    apply (erule fsteps.cases, force)
    apply (clarsimp simp del: comp_apply)
    apply (rename_tac \<gamma> lxx' sxx' cxx' \<gamma>s lyy' syy' cyy')
    apply (clarsimp simp del: comp_apply simp add: pred_executions_suc_iff)
    apply (case_tac \<gamma>)
    subgoal sorry
    apply (subgoal_tac \<open>cyy' = cxx'\<close>)
     prefer 2
      (* by determ step *)
    subgoal sorry
    apply clarsimp
    apply (frule_tac sxs=sxs and sys=sys and \<oo>=\<oo> and r=r and F=F in double_stepI, assumption)
      (* from determ assms *)
    subgoal sorry
    subgoal sorry
        (* from safe *)
    subgoal sorry
        (* from safe *)
    subgoal sorry
    apply (rename_tac \<beta> flx fly)
    apply (frule_tac sc=\<open>((_, (sxs, sys)), liftC' c)\<close> in strip_popstep)
    apply (frule_tac safe_suc_conseq(4), blast, blast, blast, blast)
    apply clarsimp
    apply (frule_tac \<gamma>s=\<gamma>s in Suc.hyps[of _ _ _ \<open>(sxl,sxs)\<close> \<open>(syl,sys)\<close> _ sx' sy' for sxl sxs syl sys])
      (* from splitting safe Suc n and framed state *)
              apply blast
             apply (clarsimp, (intro conjI; rule refl))
            apply (metis Suc.prems(4))
           apply (metis Suc.prems(5))
          apply (metis cancellative_def)
         apply (metis cancellative_def)
        apply blast
       apply (clarsimp simp add: Suc.prems(5))
       apply (drule_tac x=\<open>strip_pact \<beta>\<close> in spec, drule spec2, drule spec2, drule spec2, drule spec,
        drule mp, (rule conjI; assumption))
       apply (drule mp, assumption, drule mp, (rule conjI; assumption))
       apply (metis (lifting) cancellativeD)
      apply blast
     apply blast
    apply blast
    done
qed


theorem noninterference:
  fixes n :: nat
    and c :: \<open>('l::pre_perm_alg \<times> 's) comm\<close>
    and sx sy :: \<open>'l \<times> 's\<close>
    and r :: \<open>'s \<Rightarrow> 's \<Rightarrow> bool\<close>
    and F :: \<open>'l \<times> 's \<Rightarrow> bool\<close>
  assumes
    \<open>safe n cc zz rr gg qq SS FF\<close>
    \<open>cc = liftC' c\<close>
    \<open>zz = Inl (exch4 (sx, sy))\<close>
    \<open>rr = liftR r\<close>
    \<open>FF = liftP F \<circ> exch4\<close>
    \<open>(sx, c) \<midarrow>r, F, \<gamma>s\<rightarrow>\<^sub>f\<^sup>* (Inl sx', cx')\<close>
    \<open>(sy, c) \<midarrow>r, F, \<gamma>s\<rightarrow>\<^sub>f\<^sup>* (Inl sy', cy')\<close>
    \<open>length \<gamma>s < n\<close>
    \<open>pred_executions
      (\<lambda>(s,c).
        determ_steps \<oo> r F (unliftC c) (exch4 s) \<and>
        sec_determ_endet (unliftC c) (exch4 s))
      FF rr cc zz n\<close>
    \<open>\<forall>xl xs. F (xl, xs) \<longrightarrow> cancellative xl\<close>
    \<open>rely_obs_safe \<oo> r \<close>
    \<open>SS \<^emph>\<and> FF \<le> \<bbbA> \<oo> \<circ> exch4\<close>
  shows
    \<open>\<lblot> (=) sx' \<^emph>\<and> F \<bar> (=) sy' \<^emph>\<and> F \<rblot> \<le> \<bbbA> \<oo>\<close>
  using assms(12-) assms(5) double_determ_exec_then_safe_state[OF assms(1-11)]
  by (clarsimp simp add: sepconj_conj_def le_fun_def imp_ex_conjL)

(* TODO: write examples: (1) Arthur's nointerference, (2) observing local state *)


definition quasirefl_cl (\<open>\<^bold>\<box>\<close>) where
  \<open>quasirefl_cl p \<equiv> \<lambda>(x,y). p (x,y) \<and> p (x,x) \<and> p (y,y)\<close>

lemma quasirefl_cl_mono:
  \<open>p \<le> q \<Longrightarrow> \<^bold>\<box>p \<le> \<^bold>\<box>q\<close>
  unfolding quasirefl_cl_def
  by blast

lemma
  \<open>\<^bold>\<box>p = p \<longleftrightarrow> (\<forall>x y. p (x,y) \<longrightarrow> p (x,x) \<and> p (y,y))\<close>
  unfolding quasirefl_cl_def
  by (force simp add: fun_eq_iff)



section \<open> [OLD] Noninterference \<close>

datatype run_st = Running | Terminated | Crashed

lemma run_st_neq_iff:
  \<open>rst \<noteq> Crashed \<longleftrightarrow> rst = Running \<or> rst = Terminated\<close>
  \<open>rst \<noteq> Running \<longleftrightarrow> rst = Terminated \<or> rst = Crashed\<close>
  \<open>rst \<noteq> Terminated \<longleftrightarrow> rst = Running \<or> rst = Crashed\<close>
  by (cases rst; simp)+


type_synonym 's ptrace = \<open>'s list \<times> run_st\<close>


datatype 'a rgact = Loc 'a | Env

abbreviation \<open>LocVis a \<equiv> Loc (Vis a)\<close>
abbreviation \<open>LocTau \<equiv> Loc Tau\<close>


datatype ('s, 'a) alist1 = ASingle 's | ACons 's 'a \<open>('s, 'a) alist1\<close>

fun ahd :: \<open>('s, 'a) alist1 \<Rightarrow> 's\<close> where
  \<open>ahd (ASingle s) = s\<close>
| \<open>ahd (ACons s _ _) = s\<close>

fun ahd_act :: \<open>('s, 'a) alist1 \<Rightarrow> 'a\<close> where
  \<open>ahd_act (ASingle _) = undefined\<close>
| \<open>ahd_act (ACons _ a _) = a\<close>

definition alength :: \<open>('a, 'b) alist1 \<Rightarrow> nat\<close> where
  \<open>alength xs \<equiv> size xs - 1\<close>

lemma alength_simps[simp]:
  \<open>alength (ASingle u) = 0\<close>
  \<open>alength (ACons u w t) = Suc (alength t)\<close>
  unfolding alength_def
  using alist1.size_neq[of t]
  by force+

lemma alength_rev_iff[simp]:
  \<open>alength xs = 0 \<longleftrightarrow> (\<exists>a. xs = ASingle a)\<close>
  \<open>alength xs = Suc k \<longleftrightarrow> (\<exists>a b ys. xs = ACons a b ys \<and> alength ys = k)\<close>
  by (cases xs; simp)+

lemma alength_leq_rev_iff[simp]:
  \<open>Suc k \<le> alength xs \<longleftrightarrow> (\<exists>a b ys. xs = ACons a b ys \<and> k \<le> alength ys)\<close>
  by (cases xs; simp)
  


definition fr_opstep
  :: \<open>('l::pre_perm_alg \<times> 's \<Rightarrow> bool) \<Rightarrow>
      unit act \<Rightarrow>
      ('l \<times> 's, unit) pstate \<Rightarrow>
      ('l \<times> 's, unit) cpstate \<Rightarrow>
      bool\<close>
  where
  \<open>fr_opstep F \<alpha> sc sc' \<equiv>
    \<comment> \<open> plain opstep \<close>
    sc \<midarrow>\<alpha>\<rightarrow> sc' \<or>
    \<comment> \<open> framed opstep \<close>
    (case sc of ((hl, hs), c) \<Rightarrow>
      \<exists>hlf.
        F (hlf, hs) \<and>
        hl ## hlf \<and>
        (case sc' of
          (Inl (hl', hs'), c') \<Rightarrow>
            hl' ## hlf \<and>
            (\<alpha> = Tau \<longrightarrow> hl' = hl) \<and>
            ((hl + hlf, hs), c) \<midarrow>\<alpha>\<rightarrow> (Inl (hl' + hlf, hs'), c')
        | (Inr (), c') \<Rightarrow> 
            ((hl + hlf, hs), c) \<midarrow>\<alpha>\<rightarrow> (Inr (), c'))
    )\<close>

abbreviation pretty_fr_opstep :: \<open>_ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> _\<close> (\<open>_ \<midarrow>(_, _)\<rightarrow> _\<close> [60,0,0,60] 60) where
  \<open>s \<midarrow>F, \<beta>\<rightarrow> s' \<equiv> fr_opstep F \<beta> s s'\<close>

abbreviation pretty_no_fr_opstep :: \<open>_ \<Rightarrow> _ \<Rightarrow> bool\<close> (\<open>_ \<midarrow>(_, |)\<rightarrow>\<close> [60,0] 60) where
  \<open>s \<midarrow>F, |\<rightarrow> \<equiv> \<forall>\<beta> s'. \<not> fr_opstep F \<beta> s s'\<close>


lemma fr_opstep_from_skip_then:
  \<open>fr_opstep F \<beta> s s' \<Longrightarrow> s = (h, Skip) \<Longrightarrow> snd s' = Skip\<close>
  by (clarsimp simp add: fr_opstep_def
      split: prod.splits sum.splits unit.splits)

lemma fr_opstep_from_skip_then2[simp]:
  \<open>fr_opstep F \<beta> (h, Skip) (h', c') \<Longrightarrow> c' = Skip\<close>
  using fr_opstep_from_skip_then
  by fastforce

lemma fr_opstep_tau_preserves_state:
  \<open>s \<midarrow>F, Tau\<rightarrow> s' \<Longrightarrow> fst s' = Inl (fst s)\<close>
  unfolding fr_opstep_def
  apply (erule disjE)
   apply (force dest: opstep_tau_preserves_heap)
  apply (clarsimp split: sum.splits unit.splits)
  apply (case_tac x)
   apply (force dest: opstep_tau_preserves_heap)
  apply (force dest: opstep_tau_preserves_heap)
  done

lemma fr_opstep_tau_preserves_state_simp:
  \<open>(h, c) \<midarrow>F, Tau\<rightarrow> (h', c') \<Longrightarrow> h' = Inl h\<close>
  by (force dest: fr_opstep_tau_preserves_state)


text \<open>
  Note the the most recent state is at the *head* of the list.
  e.g. [sn, s{n-1}, ..., s1, s0].

  This is a partial trace semantics, in the style of Aczel, where environment moves are represented
  in the trace.
\<close>
inductive trsem'
  :: \<open>('l::pre_perm_alg \<times> 's \<Rightarrow> bool) \<Rightarrow>
      ('l \<times> 's \<Rightarrow> bool) \<Rightarrow>
      ('s \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow>
      ('s \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow>
      ('l \<times> 's \<Rightarrow> bool) \<Rightarrow>
      ('l \<times> 's \<Rightarrow> bool) \<Rightarrow>
      ('l \<times> 's) comm \<Rightarrow>
      ('l \<times> 's) comm \<Rightarrow>
      (('l \<times> 's) \<times> run_st, unit act rgact) alist1 \<Rightarrow>
      bool\<close>
  where
    trsem'_init[intro!]:
    \<open>p (fst sr) \<Longrightarrow>
      if c = Skip then snd sr = Terminated \<and> q (fst sr) else snd sr = Running \<Longrightarrow>
      trsem' p q r g F S c c (ASingle sr)\<close>
  | trsem'_step[intro]:
    \<open>trsem' p q r g F S cinit c t \<Longrightarrow>
      ahd t = ((hl, hs), rst) \<Longrightarrow>
      rst \<noteq> Crashed \<Longrightarrow>
      rst' = Terminated \<longrightarrow> q s \<Longrightarrow>
      (case \<gamma> of
        Loc \<alpha> \<Rightarrow> (\<exists>s'.
          ((hl, hs), c) \<midarrow>F, \<alpha>\<rightarrow> (s', c') \<and>
          (case s' of
            Inr () \<Rightarrow> hl' = hl \<and> hs' = hs \<and> rst' = Crashed
          | Inl hls' \<Rightarrow>
              hls' = (hl',hs') \<and>
              (if c' = Skip then rst' = Terminated else rst' = Running)))
      | Env \<Rightarrow> hl' = hl \<and> c' = c \<and> r hs hs' \<and> rst' = rst \<and> rst \<noteq> Crashed) \<Longrightarrow>
      trsem' p q r g F S cinit c' (ACons ((hl',hs'), rst') \<gamma> t)\<close>

inductive_cases trsem_initE[elim!]: \<open>trsem' p q r g F S cinit c (ASingle s)\<close>
inductive_cases trsem_stepE[elim!]: \<open>trsem' p q r g F S cinit c (ACons s' \<alpha> t)\<close>

definition \<open>trsem p q r g F S c \<equiv> {t. \<exists>cx. trsem' p q r g F S c cx t}\<close>


inductive trace_step_align
  :: \<open>('s, 'a act rgact) alist1 \<Rightarrow> ('s, 'a act rgact) alist1 \<Rightarrow> bool\<close>
  where
  init[intro!]: \<open>trace_step_align (ASingle s1) (ASingle s2)\<close>
| step_left_tau[intro]:
  \<open>trace_step_align t1 t2 \<Longrightarrow> trace_step_align (ACons s1 LocTau t1) t2\<close>
| step_right_tau[intro]:
  \<open>trace_step_align t1 t2 \<Longrightarrow> trace_step_align t1 (ACons s2 LocTau t2)\<close>
| step_env[intro!]:
  \<open>trace_step_align t1 t2 \<Longrightarrow>
    trace_step_align (ACons s1 Env t1) (ACons s2 Env t2)\<close>
| step_vis[intro!]:
  \<open>trace_step_align t1 t2 \<Longrightarrow>
    trace_step_align (ACons s1 (LocVis a1) t1) (ACons s2 (LocVis a2) t2)\<close>

inductive_cases trace_step_align_singleE[elim!]:
  \<open>trace_step_align (ASingle s1) (ASingle s2)\<close>
inductive_cases trace_step_align_single_leftE[elim]:
  \<open>trace_step_align (ASingle s1) t2\<close>
inductive_cases trace_step_align_single_rightE[elim]:
  \<open>trace_step_align t1 (ASingle s2)\<close>

inductive_cases trace_step_align_visE[elim!]:
  \<open>trace_step_align (ACons s1 (LocVis a1) t1) (ACons s2 (LocVis a2) t2)\<close>
inductive_cases trace_step_align_envE[elim!]:
  \<open>trace_step_align (ACons s1 Env t1) (ACons s2 Env t2)\<close>
inductive_cases trace_step_align_consE[elim]:
  \<open>trace_step_align (ACons s1 \<beta>1 t1) (ACons s2 \<beta>2 t2)\<close>

inductive_cases trace_step_align_cons_tauE[elim]:
  \<open>trace_step_align (ACons s1 \<beta>1 t1) (ACons s2 LocTau t2)\<close>
inductive_cases trace_step_align_tau_consE[elim]:
  \<open>trace_step_align (ACons s1 LocTau t1) (ACons s2 \<beta>2 t2)\<close>

lemma trace_step_align_cons_init_iff[simp]:
  \<open>trace_step_align (ACons s1 a t1) (ASingle s2)
    \<longleftrightarrow> trace_step_align t1 (ASingle s2) \<and> a = LocTau\<close>
  by (blast elim: trace_step_align.cases)

lemma trace_step_align_init_cons_iff[simp]:
  \<open>trace_step_align (ASingle s1) (ACons s2 a t2)
    \<longleftrightarrow> trace_step_align (ASingle s1) t2 \<and> a = LocTau\<close>
  by (blast elim: trace_step_align.cases)



\<comment> \<open> TODO: There's a lingering question here over how Env steps are supposed to work. \<close>
inductive trace_agree
  :: \<open>('s \<Rightarrow> 'o) \<Rightarrow> ('s, 'a act rgact) alist1 \<Rightarrow> ('s, 'a act rgact) alist1 \<Rightarrow> bool\<close>
  where
  tragree_init[intro!]: \<open>\<bbbA> \<oo> (s1,s2) \<Longrightarrow> trace_agree \<oo> (ASingle s1) (ASingle s2)\<close>
| tragree_step_left_tau[intro]:
  \<open>trace_agree \<oo> t1 t2 \<Longrightarrow> trace_agree \<oo> (ACons s1' LocTau t1) t2\<close>
| tragree_step_right_tau[intro]:
  \<open>trace_agree \<oo> t1 t2 \<Longrightarrow> trace_agree \<oo> t1 (ACons s2' LocTau t2)\<close>
| tragree_step_env[intro!]:
  \<open>trace_agree \<oo> t1 t2 \<Longrightarrow>
    \<bbbA> \<oo> (s1,s2) \<Longrightarrow>
    trace_agree \<oo> (ACons s1 Env t1) (ACons s2 Env t2)\<close>
| tragree_step_vis[intro!]:
  \<open>trace_agree \<oo> t1 t2 \<Longrightarrow>
    \<bbbA> \<oo> (s1,s2) \<Longrightarrow>
    a1 = a2 \<Longrightarrow>
    trace_agree \<oo> (ACons s1 (LocVis a1) t1) (ACons s2 (LocVis a2) t2)\<close>

inductive_cases trace_agree_initE[elim!]: \<open>trace_agree \<oo> (ASingle s1) (ASingle s2)\<close>
inductive_cases trace_agree_visE[elim!]:
  \<open>trace_agree \<oo> (ACons s1 (LocVis a1) t1) (ACons s2 (LocVis a2) t2)\<close>
inductive_cases trace_agree_envE[elim!]:
  \<open>trace_agree \<oo> (ACons s1 Env t1) (ACons s2 Env t2)\<close>

lemma agree_cons_init_iff[simp]:
  \<open>trace_agree \<oo> (ACons s1 a t1) (ASingle s2)
    \<longleftrightarrow> trace_agree \<oo> t1 (ASingle s2) \<and> a = LocTau\<close>
  by (blast elim: trace_agree.cases)

lemma agree_init_cons_iff[simp]:
  \<open>trace_agree \<oo> (ASingle s1) (ACons s2 a t2)
    \<longleftrightarrow> trace_agree \<oo> (ASingle s1) t2 \<and> a = LocTau\<close>
  by (blast elim: trace_agree.cases)


lemma alist1_le_Suc0_iff[simp]:
  fixes t :: \<open>('a,'b) alist1\<close>
  shows \<open>size t \<le> Suc 0 \<longleftrightarrow> (\<exists>a. t = ASingle a)\<close>
  by (induct t) (simp add: alist1.size_neq)+

lemma alist1_gt_Suc_iff[simp]:
  fixes t :: \<open>('a,'b) alist1\<close>
  shows
    \<open>0 < k \<Longrightarrow>
      Suc k \<le> size t \<longleftrightarrow> (\<exists>a b t'. t = ACons a b t' \<and> k \<le> size t')\<close>
  by (induct t arbitrary: k) simp+

lemma trsem'_init_skip_then:
  \<open>trsem' p q r g S F cinit c t1 \<Longrightarrow> cinit = Skip \<Longrightarrow> c = Skip\<close>
  apply (induct rule: trsem'.inducts)
   apply force
  apply (clarsimp split: rgact.splits sum.splits unit.splits)
   apply (case_tac s'; force)
  done

lemma trsem'_init_skip_then':
  \<open>trsem' p q r g S F Skip c t1 \<Longrightarrow> c = Skip\<close>
  by (simp add: trsem'_init_skip_then)

lemma ex_trsem'_init_skip_iff[simp]:
  \<open>(\<exists>c. trsem' p q r g S F Skip c t1) \<longleftrightarrow> trsem' p q r g S F Skip Skip t1\<close>
  using trsem'_init_skip_then by blast

lemma apfst_eq_conv2: "apfst f x = apfst g y \<longleftrightarrow> f (fst x) = g (fst y) \<and> snd x = snd y"
  by (cases x; cases y) clarsimp

lemma apsnd_eq_conv2:
  "apsnd f x = apsnd g y \<longleftrightarrow> f (snd x) = g (snd y) \<and> fst x = fst y"
  by (cases x; cases y) force


(* 
Let c be a simple program that operates on a single state and 
let \<oo> be  a function describing the observations the attacker can make on a given state,
the function (liftC \<oo> c) turns the program c into one that operates on a pair of states and that crashes
when run on states that are distingishable through  \<oo>. This in turn, which can be  used for info flow reasoning.



the safe judgement provides the same amount of information as a programming language semantics that 
is a tree T of all possible executions that can happen, as well as a proof that if the precondition and 
the relies, then for all possible executions in the tree
   (1) they don't fail and
   (2) the obey the guarantees and the postcondition
   (3) the frame condition is preserved


define function f ( c, n, p, r) = trees T

prove
theorems 
safe_imp_no_crash:"safe  c, n, p, r, q,g \<longrightarrow> 
  (1) the program f ( c, n, p, r) does not crash,
  (2) the program  obey the guarantees and the postcondition
  (3) the frame condition is preserved


definition noninterference is: given a pair of states s1 and s2, indistinguishable by \<oo>,
no execution of the program on s1 and s2 respectively, are pair-wise indistinguishable by \<oo> throughout execution and 
the program executions match/allign.


-------

definition noninterference is: given a pair of states, indistinguishable by \<oo>,
no execution of the program c (lifted to pairs of states) reaches a pair of states distinguishable by \<oo>.

definition noninterference on (liftC \<oo> c) is also a property s.t.
given a pair of states that are indistinguishable through \<oo>, of the program  (liftC \<oo> c) doesn't fail 
then all pairs of states throughout the 
execution of liftC \<oo> c are indistinguishable.

the noninterference judgement on (liftC \<oo> c) provides the same amount of information as a programming language semantics that 
is a tree T of all possible executions that can happen on pairs of states, as well as a proof that if the precondition and 
the relies hold and the precondition respects  \<oo>, then for all possible executions in the tree
   if the program doesn't fail 
    the indistinguishability predicate is preserved


(do we also want the frame condition to be preserved)

question
is there anything other than no-crash that is needed to prove non-interference and (e.g. there is no non-determinism), potentially?

if not,

prove 
theorem noninterference: 


If we can prove this, we are done (with the security paper).

question 
can we change liftC to not crash
then instead prove
>how can we generalise the lifting function liftC and instead of crashing 
 instantiate the guarantee in a way that enforces non-interference/indistinguishability?

then pro

If the preconditions are indistinguishable using \<oo>, and the lifted program  (liftC \<oo> c)  is safe,
and the preconditinos are indistinguishable using \<oo>.

If the preconditions are indistinguishable using \<oo>, and the lifted program  (liftC \<oo> c)  is safe,
and the preconditinos are indistinguishable using \<oo>.





properties (p, r) do not crash
these executions will 
and you can also extract a tree semantics that only contains 
split to two pieces, one is all possible executions, and the other is 
function to filter safe executions out of safe judgement
if there is no crashing anywhere 

define noninterference directly on liftC o C

lemma exact_security:
  fixes hl1 hl2 :: \<open>'l :: pre_perm_alg\<close>
    and hs1 hs2 :: 's
    and c :: \<open>('l \<times> 's, unit) comm\<close>
    and p q :: \<open>'l \<times> 's \<Rightarrow> bool\<close>
    and r g :: \<open>'s \<Rightarrow> 's \<Rightarrow> bool\<close>
  shows
  \<open>safe
      (max (alength t1) (alength t2))
      (liftC \<oo> c)
      (Inl (exch4 (fst (ahd t1), fst (ahd t2))))
      (liftR r) (liftR g)
      (liftP q \<circ> exch4)
      (liftP S \<circ> exch4) (liftP F \<circ> exch4) \<Longrightarrow> f ( c, n, p, r) 
no_crashing \<and> indistinguishable everywhere through initial_s p c  \<oo>  >
*)


(*
lemma exact security
<no_crashing \<Longrightarrow>
    t1 \<in> trsem p q r g S F c \<Longrightarrow>
    t2 \<in> trsem p q r g S F c \<Longrightarrow>
    trace_step_align t1 t2 \<Longrightarrow>
    \<lblot> p \<rblot> \<le> \<bbbA> \<oo> \<Longrightarrow>
    trace_agree (apfst \<oo>) t1 t2\<close>
*)
lemma exact_security:
  fixes hl1 hl2 :: \<open>'l :: pre_perm_alg\<close>
    and hs1 hs2 :: 's
    and c :: \<open>('l \<times> 's, unit) comm\<close>
    and p q :: \<open>'l \<times> 's \<Rightarrow> bool\<close>
    and r g :: \<open>'s \<Rightarrow> 's \<Rightarrow> bool\<close>
  shows
  \<open>safe
    (max (alength t1) (alength t2))
    (liftC \<oo> c)
    (Inl (exch4 (fst (ahd t1), fst (ahd t2))))
    (liftR r) (liftR g)
    (liftP q \<circ> exch4)
    (liftP S \<circ> exch4)
    (liftP F \<circ> exch4) \<Longrightarrow>
    t1 \<in> trsem p q r g S F c \<Longrightarrow>
    t2 \<in> trsem p q r g S F c \<Longrightarrow>
    trace_step_align t1 t2 \<Longrightarrow>
    \<lblot> p \<rblot> \<le> \<bbbA> \<oo> \<Longrightarrow>
    trace_agree (apfst \<oo>) t1 t2\<close>
proof (induct rule: trace_step_align.inducts)
  case (init s1 s2)
  then show ?case
    apply (clarsimp simp add: trsem_def sec_agree_def le_fun_def
        apfst_eq_conv2)
    apply (metis surj_pair)
    done
next
  case (step_left_tau t1 t2 s1)
  then show ?case
    apply (clarsimp simp add: trsem_def sec_agree_def le_fun_def
        apfst_eq_conv2)
    apply (frule fr_opstep_tau_preserves_state_simp)
    apply (case_tac t2)
     apply (simp, meson safe_step_SucD; fail)
    apply clarsimp
    apply (clarsimp simp add: safe_suc_iff)
    apply (rule tragree_step_left_tau)
    sorry
    apply (metis (no_types, lifting) le_Suc_eq max_def)
  done
next
  case (step_right_tau t1 t2 s2)
  then show ?case
    apply (clarsimp simp add: trsem_def sec_agree_def le_fun_def
        apfst_eq_conv2)
    apply (frule fr_opstep_tau_preserves_state_simp)
    apply (case_tac t1)
     apply (simp, meson safe_step_SucD; fail)
    apply (clarsimp simp add: safe_suc_iff)
    apply (rule tragree_step_right_tau)
    sorry
next
  case (step_env t1 t2 s1 s2)
  then show ?case
    apply (clarsimp simp add: trsem_def sec_agree_def le_fun_def
        apfst_eq_conv2)
    apply (rule tragree_step_env, blast)
    apply (clarsimp simp add: trsem_def sec_agree_def le_fun_def
        apfst_eq_conv2)
    apply (simp add: rely_preserves_agree_def)
    oops
next
  case (step_vis t1 t2 s1 a1 s2 a2)
  then show ?case sorry
qed

lemma security:
  fixes hl1 hl2 :: \<open>'l :: pre_perm_alg\<close>
    and hs1 hs2 :: 's
    and c :: \<open>('l \<times> 's, unit) comm\<close>
    and p q :: \<open>'l \<times> 's \<Rightarrow> bool\<close>
    and r g :: \<open>'s \<Rightarrow> 's \<Rightarrow> bool\<close>
  shows
  \<open>trace_step_align t1 t2 \<Longrightarrow>
    (\<And>n s.
      (liftP p \<circ> exch4) s \<Longrightarrow>
      safe n (liftC \<oo> c) (Inl s)
        (liftR r) (liftR g)
        (liftP q \<circ> exch4)
        (liftP S \<circ> exch4) (liftP F \<circ> exch4)) \<Longrightarrow>
    t1 \<in> trsem p q r g S F c \<Longrightarrow>
    t2 \<in> trsem p q r g S F c \<Longrightarrow>
    \<lblot> p \<rblot> \<le> \<bbbA> \<oo> \<Longrightarrow>
    trace_agree (apfst \<oo>) t1 t2\<close>
  sorry

end