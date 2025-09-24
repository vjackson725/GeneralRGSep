 theory Semantics
  imports "../Soundness"
begin


section \<open> RGSep-Security State Types \<close>

type_synonym ('a,'b) rgstate = \<open>(('a \<times> 'a) \<times> ('b \<times> 'b))\<close>

type_synonym ('a,'b) secstate = \<open>(('a \<times> 'b) \<times> ('a \<times> 'b))\<close>

(*
section \<open> Pred-executions \<close>

text \<open> Predicate over all states of all executions. \<close>

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
*)


section \<open> Double-state lifting \<close>

subsection \<open> exchange \<close>

definition
  \<open>exch4 abcd \<equiv> ((fst (fst abcd), fst (snd abcd)), (snd (fst abcd), snd (snd abcd)))\<close>

lemma exch4_four_apply[simp]:
  \<open>exch4 ((a,b),(c,d)) = ((a,c),(b,d))\<close>
  by (simp add: exch4_def)

lemma exch4_two_apply:
  \<open>exch4 (sx, sy) = ((fst sx, fst sy), (snd sx, snd sy))\<close>
  by (simp add: exch4_def)

lemma exch4_apply:
  \<open>exch4 abcd = ((fst (fst abcd), fst (snd abcd)), (snd (fst abcd), snd (snd abcd)))\<close>
  by (simp add: exch4_def)

lemma exch4_idem[simp]:
  \<open>exch4 (exch4 x) = x\<close>
  by (simp add: exch4_def split: prod.splits)

lemma exch4_eq_iff[simp]:
  \<open>exch4 a = exch4 b \<longleftrightarrow> a = b\<close>
  by (cases a, cases b, force simp add: exch4_def)

lemma comp_exch4_eq_iff[simp]:
  \<open>f \<circ> exch4 = g \<circ> exch4 \<longleftrightarrow> f = g\<close>
  by (simp add: fun_eq_iff, blast)

lemma prod_destruct_exch4_eq[simp]:
  \<open>fst (fst (exch4 x)) = fst (fst x)\<close>
  \<open>fst (snd (exch4 x)) = snd (fst x)\<close>
  \<open>snd (fst (exch4 x)) = fst (snd x)\<close>
  \<open>snd (snd (exch4 x)) = snd (snd x)\<close>
  by (clarsimp simp add: exch4_def)+

lemma prod_part_destruct_exch4_eq[simp]:
  \<open>fst (exch4 (ab, cd)) = (fst ab, fst cd)\<close>
  \<open>snd (exch4 (ab, cd)) = (snd ab, snd cd)\<close>
  by (simp add: exch4_def)+

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
  "_twoPredLiftBasic p" \<rightharpoonup> "(CONST pred_times) p p"
  "_twoPredLiftDouble p q" \<rightleftharpoons> "(CONST pred_times) p q"
  "_twoPredLiftL p" \<rightharpoonup> "(CONST pred_times) p \<top>"
  "_twoPredLiftR q" \<rightharpoonup> "(CONST pred_times) \<top> q"


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


subsubsection \<open> lift command to double command \<close>

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



subsubsection \<open> unlift double command to command \<close>

definition unliftC
  :: \<open>(('lx \<times> 'ly) \<times> ('sx \<times> 'sy)) comm \<Rightarrow> ('lx \<times> 'sx) comm \<times> ('ly \<times> 'sy) comm\<close>
  where
    \<open>unliftC c \<equiv>
      (map_atom (\<lambda>ar. rel_image fst (ar \<circ>\<^sub>2 exch4)) c, map_atom (\<lambda>ar. rel_image snd (ar \<circ>\<^sub>2 exch4)) c)\<close>

lemma unliftC_simps[simp]:
  \<open>unliftC Skip = (Skip, Skip)\<close>
  \<open>unliftC (ca ;; cb) =
    (let (cax, cay) = unliftC ca
       ; (cbx, cby) = unliftC cb
      in (cax ;; cbx, cay ;; cby))\<close>
  \<open>unliftC (ca \<^bold>\<sqinter> cb) =
    (let (cax, cay) = unliftC ca
       ; (cbx, cby) = unliftC cb
      in (cax \<^bold>\<sqinter> cbx, cay \<^bold>\<sqinter> cby))\<close>
  \<open>unliftC (ca \<^bold>\<box> cb) =
    (let (cax, cay) = unliftC ca
       ; (cbx, cby) = unliftC cb
      in (cax \<^bold>\<box> cbx, cay \<^bold>\<box> cby))\<close>
  \<open>unliftC (ca \<parallel> cb) =
    (let (cax, cay) = unliftC ca
       ; (cbx, cby) = unliftC cb
      in (cax \<parallel> cbx, cay \<parallel> cby))\<close>
  \<open>unliftC (DO c OD) =
    (let (cax, cay) = unliftC c
      in (DO cax OD, DO cay OD))\<close>
  \<open>unliftC \<langle>ar\<rangle> =
    ( \<langle>rel_image fst (ar \<circ>\<^sub>2 exch4)\<rangle>, \<langle>rel_image snd (ar \<circ>\<^sub>2 exch4)\<rangle> )\<close>
  by (simp add: unliftC_def)+

lemmas unliftC_simp[simp] =
  map_atom.simps(1-5,7)[of \<open>\<lambda>ar. rel_image fst (ar \<circ>\<^sub>2 exch4)\<close>,
    simplified unliftC_def[symmetric]]


lemma unliftC_rev_iff:
  \<open>unliftC c = (Skip, Skip) \<longleftrightarrow> c = Skip\<close>
  \<open>unliftC c = (cax ;; cbx, cay ;; cby) \<longleftrightarrow>
    (\<exists>ca cb. c = ca ;; cb \<and> unliftC ca = (cax, cay) \<and> unliftC cb = (cbx, cby))\<close>
  \<open>unliftC c = (cax \<^bold>\<sqinter> cbx, cay \<^bold>\<sqinter> cby) \<longleftrightarrow>
    (\<exists>ca cb. c = ca \<^bold>\<sqinter> cb \<and> unliftC ca = (cax, cay) \<and> unliftC cb = (cbx, cby))\<close>
  \<open>unliftC c = (cax \<^bold>\<box> cbx, cay \<^bold>\<box> cby) \<longleftrightarrow>
    (\<exists>ca cb. c = ca \<^bold>\<box> cb \<and> unliftC ca = (cax, cay) \<and> unliftC cb = (cbx, cby))\<close>
  \<open>unliftC c = (cax \<parallel> cbx, cay \<parallel> cby) \<longleftrightarrow>
    (\<exists>ca cb. c = ca \<parallel> cb \<and> unliftC ca = (cax, cay) \<and> unliftC cb = (cbx, cby))\<close>
  \<open>unliftC c = (DO cx OD, DO cy OD) \<longleftrightarrow>
    (\<exists>c'. c = DO c' OD \<and> unliftC c' = (cx, cy))\<close>
  \<open>unliftC c = (\<langle>arx\<rangle>, \<langle>ary\<rangle>) \<longleftrightarrow>
    (\<exists>ar. c = \<langle>ar\<rangle> \<and> arx = rel_image fst (ar \<circ>\<^sub>2 exch4) \<and> ary = rel_image snd (ar \<circ>\<^sub>2 exch4))\<close>
  by (clarsimp simp add: unliftC_def map_atom_rev_iff; blast)+

lemmas unliftC_rev_iff2 = unliftC_rev_iff[THEN trans[OF eq_commute]]


subsubsection \<open> command atoms refl. closure \<close>

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
  \<open>unliftC (liftC c) = (c, c)\<close>
  unfolding unliftC_def liftC_def'
  by (induct c) (force simp add: sec_agree_def fun_eq_iff)+

lemma reflclC_unliftC_same:
  \<open>reflclC cc \<Longrightarrow> unliftC cc = (cx, cy) \<Longrightarrow> cx = cy\<close>
  unfolding unliftC_def liftC_def
  by (induct cc arbitrary: cx cy)
    (fastforce simp add: fun_eq_iff)+

lemma reflclC_liftC_unliftC_cancel[simp]:
  \<open>reflclC cc \<Longrightarrow> liftC (fst (unliftC cc)) = cc\<close>
  unfolding unliftC_def liftC_def
  using reflclC_unliftC_same
  by (induct cc) (clarsimp simp add: fun_eq_iff; blast)+

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


subsection \<open> double atom \<close>

definition doubled_atom
  :: \<open>(('l \<times> 'l) \<times> ('s \<times> 's) \<Rightarrow> ('l \<times> 'l) \<times> ('s \<times> 's) \<Rightarrow> bool) \<Rightarrow> bool\<close>
  where
    \<open>doubled_atom qq \<equiv> (\<exists>q. qq = liftR q \<circ>\<^sub>2 exch4)\<close>

lemma all_doubled_atom_liftC_iff[simp]:
  \<open>all_atom_comm doubled_atom (liftC c)\<close>
  by (induct c)
    (force simp add: doubled_atom_def)+


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
    by (simp, metis (full_types) act.distinct(1))
next
  case (Iter ar)
  then show ?case
    by (simp, metis (full_types) act.distinct(1))
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


section \<open> Non-interference \<close>

lemma aopsteps_Skip_iif[simp]:
  \<open>(s, Skip) \<midarrow>\<rho>\<rightarrow>\<^sub>a\<^sup>* sc'' \<longleftrightarrow> sc'' = (s, Skip) \<and> \<rho> = []\<close>
  by (cases sc'', induct \<rho>; force)

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


section \<open> Jul-Aug Attempt \<close>

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
         Note that \<^emph>\<open>both\<close> programs need to be terminated. \<close>
    cx = Skip \<longrightarrow> cy = Skip \<longrightarrow> q ((slx, sly), (ssx, ssy)) \<Longrightarrow>
    \<comment> \<open> State Invariant \<close>
    I ((slx, sly), (ssx, ssy)) \<Longrightarrow>
    \<comment> \<open> Rely Steps \<close>
    (\<And>ssx' ssy'.
      R (ssx, ssy) (ssx', ssy') \<Longrightarrow>
      secure R F G I q n cc ((slx, ssx'), (sly, ssy'))) \<Longrightarrow>
    \<comment> \<open> Opsteps \<close>
    (\<And>\<pi>\<alpha> sx' sy' cx' cy'.
        ((slx, ssx), cx) \<midarrow>\<pi>\<alpha>\<rightarrow>\<^sub>a (sx', cx') \<Longrightarrow>
        ((sly, ssy), cy) \<midarrow>\<pi>\<alpha>\<rightarrow>\<^sub>a (sy', cy') \<Longrightarrow>
        (vis_aact (snd \<pi>\<alpha>) \<longrightarrow> G (ssx, ssy) (snd sx', snd sy')) \<and>
        (tau_aact (snd \<pi>\<alpha>) \<longrightarrow> fst sx' = slx \<and> fst sy' = sly) \<and>
        secure R F G I q n (cx', cy') (sx', sy') ) \<Longrightarrow>
    \<comment> \<open> Framed opsteps \<close>
    (\<And>fx fy \<pi>\<alpha> slfx' slfy' ssx' ssy' cx' cy'.
        F ((fx, fy), (ssx, ssy)) \<Longrightarrow>
        slx ## fx \<Longrightarrow>
        sly ## fy \<Longrightarrow>
        ((slx + fx, ssx), cx) \<midarrow>\<pi>\<alpha>\<rightarrow>\<^sub>a ((slfx', ssx'), cx') \<Longrightarrow>
        ((sly + fy, ssy), cy) \<midarrow>\<pi>\<alpha>\<rightarrow>\<^sub>a ((slfy', ssy'), cy') \<Longrightarrow>
        (vis_aact (snd \<pi>\<alpha>) \<longrightarrow> G (ssx, ssy) (ssx', ssy')) \<and>
        (\<exists>slx'.
          slx' ## fx \<and>
          slfx' = slx' + fx \<and>
          (\<exists>sly'.
            sly' ## fy \<and>
            slfy' = sly' + fy \<and>
            (tau_aact (snd \<pi>\<alpha>) \<longrightarrow> slx' = slx \<and> sly' = sly) \<and>
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

lemma head_atomic_opstep_vis_aact:
  \<open>sc \<midarrow>\<pi>\<alpha>\<rightarrow>\<^sub>a sc' \<Longrightarrow>
    head_atomic (snd sc) \<Longrightarrow>
    vis_aact (snd \<pi>\<alpha>)\<close>
  by (induct _ sc sc' rule: aopstep_induct) fastforce+

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
        apply (metis head_atomic_opstep_vis_aact snd_conv tau_aact_def vis_aact_simps(2-4))
        done
    next
      case (DoLoop \<pi>\<alpha> s c sc')
      then show ?case
        apply simp
        apply (case_tac \<open>vis_aact (snd \<pi>\<alpha>)\<close>)
        apply (simp, metis snd_conv)
        apply simp
        apply (metis head_atomic_opstep_vis_aact snd_conv tau_aact_def vis_aact_simps(2-4))
        done
    qed fastforce+
  }
  then show ?thesis
    using assms
    by fastforce
qed


lemma two_steps_no_aopstep_then_no_double_aopstep:
  assumes
    \<open>all_sec_determ c (sx, sy)\<close>
    \<open>(sx, c) \<midarrow>/\<rightarrow>\<^sub>a\<close>
    \<open>(sy, c) \<midarrow>/\<rightarrow>\<^sub>a\<close>
  shows
    \<open>(exch4 (sx, sy), liftC c) \<midarrow>/\<rightarrow>\<^sub>a\<close>
  using assms
proof (induct c arbitrary: sx sy)
  case (Seq ca cb)
  show ?case
    using Seq.prems
    apply (clarsimp simp add: exch4_def split: prod.splits)
    apply (metis Seq.hyps(1) exch4_two_apply prod.collapse)
    done
next
  case (Par ca cb)
  have no_step_subparts:
    \<open>(sx, ca) \<midarrow>/\<rightarrow>\<^sub>a\<close>
    \<open>(sy, ca) \<midarrow>/\<rightarrow>\<^sub>a\<close>
    \<open>(sx, cb) \<midarrow>/\<rightarrow>\<^sub>a\<close>
    \<open>(sy, cb) \<midarrow>/\<rightarrow>\<^sub>a\<close>
    using Par.prems(2-)
    by (metis no_opstep_then_no_aopstep opstep.simps(5) opstep_then_aopstep prod.exhaust_sel)+
  moreover have \<open>ca \<noteq> Skip \<or> cb \<noteq> Skip\<close>
    using Par.prems(2)
    by (clarsimp simp add: all_conj_distrib prod_eq_decompose)
  ultimately show ?case
    using Par.hyps(1-2) Par.prems(1)
    by (clarsimp simp add: exch4_def)
next
  case (Endet ca cb)
  show ?case
    using Endet.prems
    apply (clarsimp simp add: all_conj_distrib ball_conj_distrib)
    apply (intro conjI)
         apply metis
        apply metis
       apply (metis Endet.hyps(1) not_tau_aact_iff surj_pair)
      apply (metis Endet.hyps(2) not_tau_aact_iff surj_pair)
     apply (metis Endet.hyps(1) not_tau_aact_iff surj_pair)
    apply (metis Endet.hyps(2) not_tau_aact_iff surj_pair)
    done
next
  case (Iter c)
  show ?case
    using Iter.prems
    by (clarsimp simp add: all_conj_distrib ball_conj_distrib prod_eq_decompose)
qed (clarsimp simp add: all_conj_distrib)+


lemma full_sync_double_aopstep_to_aopstep:
  assumes
    \<open>(sx, c) \<midarrow>\<pi>\<alpha>\<rightarrow>\<^sub>a (sx', c')\<close>
    \<open>(sy, c) \<midarrow>\<pi>\<alpha>\<rightarrow>\<^sub>a (sy', c')\<close>
    \<open>all_sec_determ c (sx, sy)\<close>
  shows
    \<open>(exch4 (sx, sy), liftC c) \<midarrow>\<pi>\<alpha>\<rightarrow>\<^sub>a (exch4 (sx', sy'), liftC c')\<close>
  using assms
proof (induct c arbitrary: sx sy sx' sy' c' \<pi>\<alpha>)
  case (Endet c1 c2)
  then show ?case
    apply (case_tac \<open>vis_aact (snd \<pi>\<alpha>)\<close>)
     apply (simp add: vis_tau_aact_incompatible)
     apply (metis fst_conv pre_state_def snd_conv vis_aopstep_impl_atom)
    apply (simp add: vis_tau_aact_incompatible)
    apply (metis head_atomic.simps(1) head_atomic_opstep_vis_aact not_tau_aact_iff split_pairs)
    done
next
  case (Iter c)
  show ?case
    using Iter.prems
    apply (case_tac \<open>vis_aact (snd \<pi>\<alpha>)\<close>)
     apply (clarsimp simp add: vis_tau_aact_incompatible)
     apply (drule(2) Iter.hyps)
     apply force
    apply (clarsimp simp add: vis_tau_aact_incompatible)
    apply (elim disjE conjE exE; simp)
     apply clarsimp
     apply (metis two_steps_no_aopstep_then_no_double_aopstep surjective_pairing)
    apply (metis head_atomic_opstep_vis_aact not_tau_aact_iff snd_conv)
    done
qed fastforce+


subsection \<open> Safety Implies Security \<close>

theorem safety_implies_security:
  fixes n :: nat
    and cx cy :: \<open>('l::pre_perm_alg \<times> 's) comm\<close>
    and sxy :: \<open>('l, 's) secstate\<close>
    and F I q :: \<open>('l, 's) rgstate \<Rightarrow> bool\<close>
    and R G :: \<open>'s \<times> 's \<Rightarrow> 's \<times> 's \<Rightarrow> bool\<close>
  assumes
    \<open>safe R F G I q n (liftC c) (exch4 sxy)\<close>
    \<open>I \<squnion> I \<^emph>\<and> F \<le> all_sec_determ c \<circ> exch4\<close>
  shows
    \<open>secure R F G I q n (c, c) sxy\<close>
  using assms
proof (induct n arbitrary: c sxy)
  case (Suc n)

  obtain lsx lsy ssx ssy where sxy_split:
    \<open>sxy = ((lsx, ssx), (lsy, ssy))\<close>
    by (metis surjective_pairing)

  note Suc_ih = Suc.hyps[where sxy=\<open>((lsx', lsy'), (ssx', ssy'))\<close> for lsx' lsy' ssx' ssy',
      simplified sxy_split exch4_four_apply]
  note suc_prem_safe =
    safe_sucD(1)[OF Suc.prems(1), simplified fst_conv snd_conv sxy_split exch4_four_apply]
    safe_sucD(2)[OF Suc.prems(1), simplified fst_conv snd_conv sxy_split exch4_four_apply]
    safe_sucD(3)[OF Suc.prems(1), where ?fs=\<open>(fsx, fsy)\<close> for fsx fsy,
      simplified fst_conv snd_conv sxy_split exch4_apply plus_prod_def]

  show ?case
    using Suc.prems(2) safe_then_state_inv[OF Suc.prems(1)] safe_then_postcond[OF Suc.prems(1)]
      sxy_split
    apply (clarsimp simp del: sup_apply comp_apply)
    apply (rule secure_suc)
      (* subgoals: destructuring *)
          apply (simp; fail)
         apply (simp add: prod_eq_decompose; fail)
      (* term *)
        apply blast
      (* subgoal: invariant *)
       apply blast
      (* subgoal: rely *)
      apply (frule suc_prem_safe(1), blast)
      apply (force intro: Suc_ih)
      (* subgoal: double-step *)
     apply (frule_tac sx=\<open>(lsx, ssx)\<close> and sy=\<open>(lsy, ssy)\<close> in
        all_sec_determ_same_act_implies_same_comm, force, force)
     apply (frule_tac sx=\<open>(lsx, ssx)\<close> and sy=\<open>(lsy, ssy)\<close> in full_sync_double_aopstep_to_aopstep,
        force, force)
     apply (simp del: comp_apply add: exch4_two_apply)
     apply (frule suc_prem_safe(2)[OF aopstep_then_opstep])
     apply (intro conjI)
       apply force
      apply force
     apply (frule aopstep_preserves_all_sec_determ)
     apply (clarsimp simp del: comp_apply)
     apply (rule Suc_ih, assumption)
     apply (meson order.trans le_exch4_shunt le_supI; fail)
        (* subgoal: framed double-step *)
    apply (subgoal_tac \<open>(I \<^emph>\<and> F) ((lsx + fx, lsy + fy), (ssx, ssy))\<close>)
     prefer 2
     apply (rule sepconj_conjI, assumption, assumption, force, force)
    apply (frule_tac sx=\<open>(lsx + fx, ssx)\<close> and sy=\<open>(lsy + fy, ssy)\<close> in
        all_sec_determ_same_act_implies_same_comm, assumption)
     apply (force simp add: exch4_two_apply)
    apply (frule_tac sx=\<open>(lsx + fx, ssx)\<close> and sy=\<open>(lsy + fy, ssy)\<close> in
        full_sync_double_aopstep_to_aopstep)
      apply force
     apply force
    apply (clarsimp simp del: comp_apply)
    apply (frule suc_prem_safe(3)[OF aopstep_then_opstep])
      apply force
     apply force
    apply (frule aopstep_preserves_all_sec_determ)
    apply (clarsimp simp del: comp_apply)
    apply (frule Suc_ih)
     apply (meson order.trans le_exch4_shunt le_supI; fail)
    apply (frule aopstep_then_opstep)
    apply (clarsimp simp del: comp_apply)
    apply blast
    done
qed force


(*
section \<open> Scratch Space \<close>

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
      apply (metis head_atomic_implies_all_steps_vis pre_state_def split_pairs vis_aopstep_impl_atom)
     apply clarsimp
     apply (metis head_atomic_implies_all_steps_vis pre_state_def split_pairs vis_aopstep_impl_atom)
    apply clarsimp
    apply (metis Endet.hyps(1,2) fst_conv snd_conv head_atomic_implies_all_steps_vis
        not_tau_aact_iff pre_state_def vis_aopstep_impl_atom)
    done
next
  case (Iter c)
  show ?case
    using Iter.prems
    by (simp del: split_paired_All
        add: head_atomic_nostep_iff_state_not_in_head_guards,
        metis Iter.hyps state_not_in_head_guards_then_no_aopstep)
qed simp+

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

(*
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
*)



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
*)

end