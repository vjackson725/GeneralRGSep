theory SecurityEx
  imports "../sec/Semantics"
begin

(* TODO: move *)

lemma eq_rtimes_R_iff:
  \<open>((=) \<times>\<^sub>R r) s s' \<longleftrightarrow> r (snd s) (snd s') \<and> fst s = fst s'\<close>
  by (cases s, cases s', force)

lemma top_rtimes_R_iff:
  \<open>(\<top> \<times>\<^sub>R r) s s' \<longleftrightarrow> r (snd s) (snd s')\<close>
  by (cases s, cases s', force)


definition
  \<open>atom_rel c \<equiv> THE ar. c = \<langle>ar\<rangle>\<close>

abbreviation(input)
  \<open>atom_guard c \<equiv> pre_state (atom_rel c)\<close>

lemma atom_rel_atom_eq[simp]:
  \<open>atom_rel \<langle>ar\<rangle> = ar\<close>
  by (simp add: atom_rel_def)


lemma sepconj_comp_exch4_distrib:
  \<open>(p \<^emph> q) \<circ> exch4 = (p \<circ> exch4) \<^emph> (q \<circ> exch4)\<close>
  by (force simp add: fun_eq_iff sepconj_def)

lemma sp_times_distrib[simp]:
  \<open>sp (Ra \<times>\<^sub>R Rb) (pa \<times>\<^sub>P pb) = sp Ra pa \<times>\<^sub>P sp Rb pb\<close>
  by (force simp add: sp_def fun_eq_iff)

lemma sp_rtrancl_times_semidistrib:
  \<open>sp (Ra \<times>\<^sub>R Rb)\<^sup>*\<^sup>* (pa \<times>\<^sub>P pb) \<le> sp Ra\<^sup>*\<^sup>* pa \<times>\<^sub>P sp Rb\<^sup>*\<^sup>* pb\<close>
  by (metis rel_times_rtranclp_semidistrib sp_rel_mono sp_times_distrib)

lemma sswa_rel_times_prod_times_exch4_semidistrib:
  \<open>sswa (Ra \<times>\<^sub>R Rb) (\<lblot> p \<rblot>\<^sub>\<ddagger>) \<le> (sswa Ra p \<times>\<^sub>P sswa Rb p) \<circ> exch4\<close>
  oops

lemma rel_times_sup_semidistrib:
  \<open>(ra \<times>\<^sub>R rb) \<squnion> (ra \<times>\<^sub>R rb) \<le> (ra \<squnion> rb) \<times>\<^sub>R (ra \<squnion> rb)\<close>
  by (simp add: le_fun_def)

lemma sp_exch4_of_rel_Times_eq[simp]:
  \<open>sp ((r \<times>\<^sub>R r) \<circ>\<^sub>2 exch4) \<lblot> p \<rblot>\<^sub>\<ddagger> = \<lblot> sp r p \<rblot>\<^sub>\<ddagger>\<close>
  (* by (force simp add: fun_eq_iff sp_def) *)
  oops

definition RelAssert :: \<open>(('l, 's) rgstate \<Rightarrow> bool) \<Rightarrow> ('l, 's \<times> fail_st) rgstate comm\<close> where
  \<open>RelAssert p \<equiv>
    \<langle>\<lambda>(l, ((sx,flx), (sy,fly))) (l', (sx',flx'), (sy',fly')).
      l' = l \<and> sx' = sx \<and> sy' = sy \<and>
        ((p (l,(sx,sy)) \<or> flx = Failed \<or> fly = Failed) \<and> flx' = flx \<and> fly' = fly \<or>
          flx = Running \<and> fly = Running \<and> \<not> p (l,(sx,sy)) \<and> flx' = Failed \<and> fly' = Failed)\<rangle>\<close>

definition Output :: \<open>('l \<times> 's \<Rightarrow> 'v) \<Rightarrow> ('l, 's \<times> fail_st) rgstate comm\<close> where
  \<open>Output h \<equiv> RelAssert (\<bbbA>\<^sub>\<ddagger> h)\<close>


definition purely_relational
  :: \<open>(('l, 's) rgstate \<Rightarrow> ('l, 's) rgstate \<Rightarrow> bool) \<Rightarrow> bool\<close>
  where
    \<open>purely_relational ar \<equiv>
      (\<forall>z x' y'. (ar \<circ>\<^sub>2 exch4) (z,z) (x',y') \<longrightarrow> x' = z \<and> y' = z)\<close>

definition purely_relational2
  :: \<open>(('l, 's) rgstate \<Rightarrow> ('l, 's) rgstate \<Rightarrow> bool) \<Rightarrow> bool\<close>
  where
    \<open>purely_relational2 ar \<equiv>
      (\<forall>xa ya xa' ya' xb yb xb' yb'.
        (ar \<circ>\<^sub>2 exch4) (xa, ya) (xa', ya') \<longrightarrow>
        (ar \<circ>\<^sub>2 exch4) (xb, yb) (xb', yb') \<longrightarrow>
        (ar \<circ>\<^sub>2 exch4) (xa, yb) (xa', yb') \<and>
        (ar \<circ>\<^sub>2 exch4) (xb, ya) (xb', ya'))\<close>

lemma
  \<open>(\<forall>x y x' y'. (ar \<circ>\<^sub>2 exch4) (x, y) (x', y') \<longrightarrow> (ar \<circ>\<^sub>2 exch4) (y, x) (y', x')) \<Longrightarrow>
    (\<forall>x y x' y'. (ar \<circ>\<^sub>2 exch4) (x, x) (x', y') \<longrightarrow>
      (ar \<circ>\<^sub>2 exch4) (x, x) (x', x') \<and> (ar \<circ>\<^sub>2 exch4) (x, x) (y', y')) \<Longrightarrow>
    purely_relational2 ar \<Longrightarrow>
    purely_relational ar\<close>
  unfolding purely_relational_def purely_relational2_def
  oops

lemma purely_relational_output:
  \<open>purely_relational (atom_rel (Output h))\<close>
  unfolding Output_def RelAssert_def sec_agree_exch4_def sec_agree_def
  by (simp add: purely_relational_def fun_eq_iff)

lemma
  \<open>purely_relational (atom_rel (Await (\<bbbA> h)))\<close>
  unfolding Await_def purely_relational_def
  by (clarsimp simp add: fun_eq_iff)


section \<open> Secure If-statement \<close>

definition \<open>SecIfThenElse p ct cf \<equiv> Await (\<lblot> p \<rblot>) ;; ct \<^bold>\<box> Await (\<lblot> -p \<rblot>) ;; cf\<close>

lemma ecIfThenElse_inject[simp]:
  \<open>SecIfThenElse p1 ct1 cf1 = SecIfThenElse p2 ct2 cf2 \<longleftrightarrow> p1 = p2 \<and> ct1 = ct2 \<and> cf1 = cf2\<close>
  by (force simp add: SecIfThenElse_def fun_eq_iff)

lemma SecIfThenElse_distinct[simp]:
  \<open>SecIfThenElse p ct cf \<noteq> Skip\<close>
  \<open>SecIfThenElse p ct cf \<noteq> c1 ;; c2\<close>
  \<open>SecIfThenElse p ct cf \<noteq> c1 \<parallel> c2\<close>
  \<open>SecIfThenElse p ct cf \<noteq> \<langle>ar\<rangle>\<close>
  \<open>Skip \<noteq> SecIfThenElse p ct cf\<close>
  \<open>c1 ;; c2 \<noteq> SecIfThenElse p ct cf\<close>
  \<open>c1 \<parallel> c2 \<noteq> SecIfThenElse p ct cf\<close>
  \<open>\<langle>ar\<rangle> \<noteq> SecIfThenElse p ct cf\<close>
  by (simp add: SecIfThenElse_def)+

lemma rgsat_if_then_else:
  assumes
    \<open>rel_liftL (sswa R p \<squnion> sswa R p \<^emph>\<and> F) \<sqinter> (=) \<le> \<top> \<times>\<^sub>R G\<close>
    and tt_guard_frame_cond:
    \<open>\<forall>f\<le>F. (sswa R p \<^emph>\<and> f) \<sqinter> pp \<le> (sswa R p \<sqinter> pp) \<^emph>\<and> f\<close>
    and ff_guard_frame_cond:
    \<open>\<forall>f\<le>F. (sswa R p \<^emph>\<and> f) \<sqinter> -pp \<le> (sswa R p \<sqinter> -pp) \<^emph>\<and> f\<close> 
    and body_assms:
    \<open>R, G, Ia, F, T \<turnstile> { sswa R (sswa R p \<sqinter> pp) } ctt { qa }\<close>
    \<open>R, G, Ib, F, T \<turnstile> { sswa R (sswa R p \<sqinter> -pp) } cff { qb }\<close>
    and misc_assms:
    \<open>T RGSepAtom\<close>
    \<open>T RGSepEndet\<close>
    \<open>T RGSepSeq\<close>
    \<open>sswa R p \<le> I\<close>
    \<open>Ia \<le> I\<close>
    \<open>Ib \<le> I\<close>
    \<open>qa \<le> q\<close>
    \<open>qb \<le> q\<close>
  shows
    \<open>R, G, I, F, T \<turnstile> { p } IfThenElse pp ctt cff { q }\<close>
  using misc_assms
  unfolding IfThenElse_def
proof (intro rgsat_endet[OF rgsat_seq rgsat_seq order.refl order.refl,
      where I=I and Ia=\<open>sswa R p \<squnion> Ia\<close> and Ib=\<open>sswa R p \<squnion> Ib\<close>])
  show \<open>R, G, sswa R p, F, T \<turnstile> { p } Await pp { sswa R (sswa R p \<sqinter> pp) }\<close>
    using misc_assms assms(1) tt_guard_frame_cond
    apply (intro rgsat_await; simp)
     apply (simp add: inf_sup_aci(2,3) le_infI2 rel_image_snd_galois rel_liftL_conj_eq; fail)
    apply (metis order.refl inf_sup_ord(1) wlp_weaker_iff_sp_stronger wssa_over_sswa_eq)
    done
  show \<open>R, G, Ia, F, T \<turnstile> { sswa R (sswa R p \<sqinter> pp) } ctt { qa }\<close>
    using body_assms
    by blast
  show \<open>R, G, sswa R p, F, T \<turnstile> { p } Await (- pp) { sswa R (sswa R p \<sqinter> -pp) }\<close>
    using ff_guard_frame_cond misc_assms assms
    apply (intro rgsat_await; simp)
     apply (simp add: inf.assoc inf.left_commute le_infI2 rel_image_snd_galois
        rel_liftL_conj_distrib; fail)
    apply (meson le_infI1 relyrel_trans transp_relcompp wlp_sp_weak_absorb
        wlp_weaker_iff_sp_stronger; fail)
    done
  show \<open>R, G, Ib, F, T \<turnstile> { sswa R (sswa R p \<sqinter> -pp) } cff { qb }\<close>
    using body_assms
    by blast
  show \<open>sswa R p \<squnion> Ia \<le> I\<close>
    using misc_assms
    by simp
  show \<open>sswa R p \<squnion> Ib \<le> I\<close>
    using misc_assms
    by simp
qed simp+

lemma secure_if_statement_rule:
  assumes \<open>R, G, I, F, C \<turnstile> { p } c { q }\<close>
  shows \<open>liftR R, liftR G, \<lblot> I \<rblot>\<^sub>\<ddagger>, \<lblot> F \<rblot>\<^sub>\<ddagger>, C \<circ> unliftC \<turnstile> { \<lblot> p \<rblot>\<^sub>\<ddagger> } liftC c { \<lblot> q \<rblot>\<^sub>\<ddagger> }\<close>




section \<open> Old things \<close>


lemma
  \<open>purely_relational (atom_rel (\<langle> ar \<rangle>)) \<Longrightarrow> unliftC2 \<langle> ar \<rangle> = \<langle> case_prod (=) \<rangle>\<close>
  unfolding Await_def purely_relational_def
  by (clarsimp simp add: fun_eq_iff)













lemma helper:
  \<open>A \<and> B \<and> C \<or> B \<and> C \<longleftrightarrow> B \<and> C\<close>
  by blast

lemma
  \<open>unliftC (RelAssert p :: ('l, 's \<times> fail_st) rgstate comm) =
    ( \<langle>\<lambda>(l,(s,fl)) (l',(s',fl')).
        l' = l \<and> s' = s \<and>
        (fl = Failed \<longrightarrow> fl' = Running \<longrightarrow> False) \<and>
        (fl = Running \<longrightarrow> fl' = Failed \<longrightarrow> (\<exists>ly sy. \<not> p ((l, ly), (s, sy))))
      \<rangle>
    , \<langle>\<lambda>(l,(s,fl)) (l',(s',fl')).
        l' = l \<and> s' = s \<and>
          (fl = fl' \<or>
            fl = Running \<and> fl' = Failed \<and> (\<exists>lx sx. \<not> p ((lx, l), (sx, s))
          ))
      \<rangle>
    )\<close>
  by (force simp add: RelAssert_def fun_eq_iff all_fail_st_eq ex_fail_st_eq)

section \<open> Examples \<close>


lemma
  shows \<open>liftR R, liftR G, \<lblot> I \<rblot>\<^sub>\<ddagger>, \<lblot> F \<rblot>\<^sub>\<ddagger>, C \<circ> unliftC \<turnstile>\<^sub>f { \<lblot> p \<rblot>\<^sub>\<ddagger> } liftC c { \<lblot> q \<rblot>\<^sub>\<ddagger> }\<close>

lemma double_program_lifting':
  assumes \<open>R, G, I, F, C \<turnstile> { p } c { q }\<close>
  shows \<open>liftR R, liftR G, \<lblot> I \<rblot>\<^sub>\<ddagger>, \<lblot> F \<rblot>\<^sub>\<ddagger>, C \<circ> unliftC \<turnstile> { \<lblot> p \<rblot>\<^sub>\<ddagger> } liftC c { \<lblot> q \<rblot>\<^sub>\<ddagger> }\<close>
  using assms
proof (induct rule: rgsat.induct)
  case (rgsat_skip R p q I C G F)
  then show ?case
    apply (clarsimp simp del: comp_apply)
    apply (rule rgsat.rgsat_skip)
      apply (clarsimp simp del: comp_apply)
      apply (frule predicate1D[OF sswa_rel_times_prod_times_exch4_semidistrib])
      apply (simp add: le_fun_def; fail)
     apply (clarsimp simp del: comp_apply)
     apply (frule predicate1D[OF sswa_rel_times_prod_times_exch4_semidistrib])
     apply (simp add: le_fun_def; fail)
    apply (simp; fail)
    done
next
  case (rgsat_iter c R G i I F C p q)
  moreover have
    \<open>R \<times>\<^sub>R R, G \<times>\<^sub>R G, \<lblot> I \<rblot>\<^sub>\<ddagger>, \<lblot> F \<rblot>\<^sub>\<ddagger>, C \<circ> unliftC \<turnstile> { sswa (R \<times>\<^sub>R R) \<lblot> i \<rblot>\<^sub>\<ddagger> } liftC c { \<lblot> i \<rblot>\<^sub>\<ddagger> }\<close>
    using rgsat_iter.hyps(2)
    apply (meson le_disj_eq_absorb rgsat_weaken sswa_rel_times_prod_times_exch4_semidistrib)
    done
  ultimately show ?case
    apply (clarsimp simp del: comp_apply)
    apply (rule rgsat.rgsat_iter[where i=\<open>\<lblot> i \<rblot>\<^sub>\<ddagger>\<close>])
       apply assumption
      apply (clarsimp simp del: comp_apply)
      apply (frule predicate1D[OF sswa_rel_times_prod_times_exch4_semidistrib])
      apply (simp add: le_fun_def; fail)
     apply (clarsimp simp del: comp_apply)
     apply (frule predicate1D[OF sswa_rel_times_prod_times_exch4_semidistrib])
     apply (simp add: le_fun_def; fail)
    apply (simp; fail)
    done
next
  case (rgsat_seq ca R G p pp Ia F C cb q Ib I)
  note ih = rgsat_seq.hyps(2,4)
  then show ?case
    using rgsat_seq.prems rgsat_seq.hyps(5-)
    apply (clarsimp simp del: comp_apply)
    apply (rule rgsat.rgsat_seq)
        apply force+
    done
next
  case (rgsat_indet ca r Ga p qa Ia F C cb Gb qb Ib G q I)
  note ih = rgsat_indet.hyps(2,4)
  then show ?case
    using rgsat_indet.prems rgsat_indet.hyps(5-)
    apply (clarsimp simp del: comp_apply)
    apply (rule rgsat.rgsat_indet)
            apply force+
    done
next
  case (rgsat_endet ca r Ga p qa Ia F C cb Gb qb Ib G q I)
  note ih = rgsat_endet.hyps(2,4)
  then show ?case
    using rgsat_endet.prems rgsat_endet.hyps(5-)
    apply (clarsimp simp del: comp_apply)
    apply (rule rgsat.rgsat_endet)
            apply force+
    done
next
  case (rgsat_par ca R Gb Ga pa qa Ia Ib F C cb pb qb G p q I)
  note ih = rgsat_par.hyps(2,4)
  show ?case
    using rgsat_par.prems rgsat_par.hyps(5-)
    apply (clarsimp simp del: comp_apply sup_apply)
    apply (rule rgsat.rgsat_par[where Gb=\<open>Gb \<times>\<^sub>R Gb\<close> and pa=\<open>\<lblot> pa \<rblot>\<^sub>\<ddagger>\<close> and qa=\<open>\<lblot> qa \<rblot>\<^sub>\<ddagger>\<close>
          and Ia=\<open>\<lblot> Ia \<rblot>\<^sub>\<ddagger>\<close> and Ib=\<open>\<lblot> Ib \<rblot>\<^sub>\<ddagger>\<close>])
           apply (rule rgsat.rgsat_weaken[OF ih(1)])
                apply blast
               apply blast
              apply (clarsimp simp del: sup_apply simp add: rel_Times_mono; fail)
             apply (rule order.refl)
            apply (rule order.refl)
           apply (metis predTimesExch4_sup_semidistrib predTimesExch4_sepconj_conj_distrib)
          apply (rule rgsat.rgsat_weaken[OF ih(2)])
               apply blast
              apply blast
             apply (clarsimp simp del: sup_apply simp add: rel_Times_mono; fail)
            apply (rule order.refl)
           apply (rule order.refl)
          apply (metis predTimesExch4_sup_semidistrib predTimesExch4_sepconj_conj_distrib)
         apply (simp add: rel_Times_mono; fail)
        apply (simp add: rel_Times_mono; fail)
       apply (metis predTimesExch4_mono predTimesExch4_sepconj_conj_distrib)
      (* post-condition *)
      apply (frule predTimesExch4_mono[where q=q])
      apply (rule order.trans[rotated], assumption)
      apply (simp add: predTimesExch4_sepconj_conj_distrib del: comp_apply)
      apply (rule sepconj_conj_mono)
       apply (rule order.trans[OF _ sswa_rel_times_prod_times_exch4_semidistrib])
       apply (simp add: rel_Times_mono sswa_rel_mono; fail)
      apply (rule order.trans[OF _ sswa_rel_times_prod_times_exch4_semidistrib])
      apply (meson rel_Times_mono sswa_rel_mono sup.boundedI sup.cobounded1 sup.cobounded2; fail)
      (* invariant *)
     apply (frule predTimesExch4_mono[where q=I])
     apply (rule order.trans[rotated], assumption)
     apply (simp add: predTimesExch4_sepconj_conj_distrib del: comp_apply)
     apply (rule sepconj_conj_mono)
      apply (rule order.trans[OF _ sswa_rel_times_prod_times_exch4_semidistrib])
      apply (simp add: rel_Times_mono sswa_rel_mono; fail)
     apply (rule order.trans[OF _ sswa_rel_times_prod_times_exch4_semidistrib])
     apply (simp add: rel_Times_mono sswa_rel_mono; fail)
      (* command predicate *)
    apply (simp; fail)
    done
next
  case (rgsat_atom p' R p q q' ar G F I C)
  then show ?case
    using rgsat_atom.prems
    apply (clarsimp simp del: comp_apply sup_apply)
    apply (rule rgsat.rgsat_atom[where p=\<open>\<lblot> p \<rblot>\<^sub>\<ddagger>\<close> and q=\<open>\<lblot> q \<rblot>\<^sub>\<ddagger>\<close>])
            apply (meson order.trans predTimesExch4_mono sswa_rel_times_prod_times_exch4_semidistrib
        wlp_weaker_iff_sp_stronger; fail)
           apply (meson order.trans predTimesExch4_mono sswa_rel_times_prod_times_exch4_semidistrib;
        fail)
      (* sp *)
          apply (simp add: predTimesExch4_mono; fail)
      (* guar *)
         apply (force simp add: le_fun_def; fail)
      (* framed sp *)
        apply (clarsimp simp add: le_fun_def sp_def sepconj_conj_def imp_ex_conjL imp_conjL)
        apply (rename_tac ssfa' ssfb' lsa' lsb' ssa ssb lsa fa lsb fb)
        apply (frule_tac x=\<open>(=) (fa, ssa)\<close> in spec, drule mp[of \<open>\<forall>x y. _ x y \<longrightarrow> F (x,y)\<close>], metis)
        apply (frule_tac x=\<open>(=) (fb, ssb)\<close> in spec, drule mp[of \<open>\<forall>x y. _ x y \<longrightarrow> F (x,y)\<close>], metis)
        apply (metis prod.inject)
      (* framed guar *)
       apply (clarsimp simp add: le_fun_def exch4_def sepconj_conj_def imp_ex_conjL imp_conjL; fail)
      (* invariant 1 *)
      apply (meson order.trans predTimesExch4_mono sswa_rel_times_prod_times_exch4_semidistrib; fail)
      (* invariant 2 *)
     apply (meson order.trans predTimesExch4_mono sswa_rel_times_prod_times_exch4_semidistrib; fail)
    apply force
    done
next
  case (rgsat_frame c R G p q I F F' C)
  then show ?case sorry
next
  case (rgsat_weaken c r' g' p' q' I' F' C p q r g I F)
  then show ?case sorry
next
  case (rgsat_Disj p' P c R G q I F C)
  then show ?case sorry
next
  case (rgsat_Conj \<I> I' \<G> G' Q q' c R p F C)
  then show ?case sorry
qed



subsection \<open> SecCSL example \<close>

datatype lock = Locked | Unlocked
datatype 'v s_val = SVal 'v | SLock lock


definition Acquire :: \<open>'x \<Rightarrow> ('l \<times> (('x \<Rightarrow> 'v s_val) \<times> bool)) comm\<close> where
  \<open>Acquire x \<equiv>
    \<langle>\<lambda>(ls, (m, f)) (ls', (m', f')).
      ((\<nexists>lk. m x = SLock lk) \<or> f) \<and> m' = m \<and> f' = True \<or>
      m x = SLock Unlocked \<and> \<not> f \<and> m' = m(x := SLock Locked) \<and> f' = f
      \<comment> \<open> m x = SLock Locked ~> blocked \<close>
    \<rangle>\<close>

lemma guard_Acquire[simp]:
  \<open>atom_guard (Acquire x) s \<longleftrightarrow>
    (\<forall>lk. fst (snd s) x \<noteq> SLock lk) \<or>
      snd (snd s) \<or>
      \<not> snd (snd s) \<and> fst (snd s) x = SLock Unlocked\<close>
  by (simp add: atom_guard_def Acquire_def pre_state_def split: prod.splits, blast)


definition Release :: \<open>'x \<Rightarrow> ('l \<times> (('x \<Rightarrow> 'v s_val) \<times> bool)) comm\<close> where
  \<open>Release x \<equiv>
    \<langle>\<lambda>(ls, (m, f)) (ls', (m', f')).
      (m x \<noteq> SLock Locked \<or> f) \<and> m' = m \<and> f' = True \<or>
      m x = SLock Locked \<and> \<not> f \<and> m' = m(x := SLock Unlocked) \<and> f' = f
    \<rangle>\<close>

lemma guard_Release[simp]:
  \<open>atom_guard (Release x) s \<longleftrightarrow> True\<close>
  by (simp add: atom_guard_def Release_def pre_state_def split: prod.splits, blast)


definition Load
  :: \<open>'x \<Rightarrow> 'p \<Rightarrow> (('p \<rightharpoonup> 'v discr) \<times> (('x \<Rightarrow> ('v discr) s_val) \<times> bool)) comm\<close>
  where
    \<open>Load x p \<equiv> undefined\<close>

definition Store
  :: \<open>'p \<Rightarrow> 'x \<Rightarrow> (('p \<rightharpoonup> 'v discr) \<times> (('x \<Rightarrow> ('v discr) s_val) \<times> bool)) comm\<close>
  where
    \<open>Store p x \<equiv> undefined\<close>


definition procA :: \<open>string \<Rightarrow> ((nat \<rightharpoonup> 'v discr) \<times> ((string \<Rightarrow> ('v discr) s_val) \<times> bool)) comm\<close> where
  \<open>procA x \<equiv>
    Acquire ''mutex'' ;;
    Load x 0 ;;
    Store 0 x ;;
    Release ''mutex''\<close>

definition
  \<open>prog_mutex_contest \<equiv> procA ''x'' \<parallel> procA ''y''\<close>


definition mdefined :: \<open>'x \<Rightarrow> ('x \<rightharpoonup> 'v) \<Rightarrow> bool\<close> where
  \<open>mdefined x \<equiv> \<lambda>m. m x \<noteq> None\<close>

definition locked :: \<open>'x \<Rightarrow> ('x \<Rightarrow> 'v s_val) \<Rightarrow> bool\<close> where
  \<open>locked x \<equiv> \<lambda>f. f x = SLock Locked\<close>

definition unlocked :: \<open>'x \<Rightarrow> ('x \<Rightarrow> 'v s_val) \<Rightarrow> bool\<close> where
  \<open>unlocked x \<equiv> \<lambda>f. f x = SLock Unlocked\<close>

definition rinv :: \<open>('l::multiunit_sep_alg \<times> 's \<Rightarrow> bool) \<Rightarrow> ('l \<Rightarrow> bool) \<Rightarrow> ('l \<times> 's \<Rightarrow> bool)\<close> where
  \<open>rinv p pl \<equiv> (\<lambda>s. if p s then pl (fst s) else emp (fst s))\<close>

lemma prog_mutex_contest:
  fixes I :: \<open>(nat \<rightharpoonup> 'v discr) \<times> ((string \<Rightarrow> 'v discr s_val) \<times> bool) \<Rightarrow> bool\<close>
  defines
    \<open>I \<equiv> \<S> (\<top> \<times>\<^sub>P Not) \<sqinter> (rinv (\<S> (locked ''mutex'' \<times>\<^sub>P \<top>)) (mdefined 0) \<^emph>\<and> \<top>)\<close>
  shows
    \<open>(=), \<top>, I, \<top>, \<top> \<turnstile> { \<L> emp } prog_mutex_contest { \<L> emp }\<close>
  unfolding prog_mutex_contest_def
  sorry

text \<open> There's no (non-parallelism) non-determinism, thus it's always security deterministic. \<close>
lemma security_determ_prog_mutex_contest:
  \<open>\<top> \<le> sec_determ prog_mutex_contest\<close>
  by (force simp add: prog_mutex_contest_def)

lemma secure_prog_mutex_contest:
  defines
    \<open>I \<equiv> \<S> (\<top> \<times>\<^sub>P Not) \<sqinter> (rinv (\<S> (locked ''mutex'' \<times>\<^sub>P \<top>)) (mdefined 0) \<^emph>\<and> \<top>)\<close>
  shows
    \<open>(=), \<top>, \<lblot> I \<rblot>\<^sub>\<ddagger>, \<top>, \<top> \<turnstile> { \<lblot> \<L> emp \<rblot>\<^sub>\<ddagger> } liftC prog_mutex_contest { \<lblot> \<L> emp \<rblot>\<^sub>\<ddagger> }\<close>
  using assms
  by (intro double_program_lifting[OF prog_mutex_contest]) force+


subsection \<open> Wordle \<close> (* TODO *)

type_synonym varnm = \<open>char list\<close>
type_synonym wordle_ls = \<open>varnm \<rightharpoonup> char list discr \<times> munit\<close>
type_synonym wordle_ss = \<open>varnm \<Rightarrow> char list\<close>

definition wordle_output
  :: \<open>wordle_ls \<times> wordle_ss \<Rightarrow> bool \<times> nat set\<close>
  where
  \<open>wordle_output \<equiv> \<lambda>(ls, ss).
    let word = the_discr (fst (the (ls ''word'')))
      ; guess = ss ''guess''
    in
    (mset word = mset guess,
      {i. i \<le> max (length word) (length guess) \<longrightarrow> word ! i = guess ! i})\<close>

lemma wordle_output_local_reduce:
  \<open>lsa ## lsb \<Longrightarrow>
    lsa ''word'' \<noteq> None \<Longrightarrow>
    wordle_output (lsa + lsb, ss) = wordle_output (lsa, ss)\<close>
  apply (clarsimp simp add: wordle_output_def Let_def disjoint_fun_def)
  apply (subgoal_tac \<open>lsa ''word'' ## lsb ''word''\<close>)
   apply force
  apply metis
  done

lemma wordle_output_agree_frame_local:
  fixes p F :: \<open>(wordle_ls \<times> wordle_ls) \<times> (wordle_ss \<times> wordle_ss) \<Rightarrow> bool\<close>
  assumes \<open>post_state (curry p) \<le> post_state (curry F)\<close>
    and \<open>p \<le> \<lblot>\<lambda>(ls, ss). ls ''word'' \<noteq> None\<rblot> \<circ> exch4\<close>
  shows \<open>frame_local F p (\<bbbA> wordle_output \<circ> exch4)\<close>
  using assms
  apply (simp add: frame_local_def le_fun_def post_state_def)
  apply (rule conjI[rotated], blast)
  apply (clarsimp simp add: sec_agree_def sepconj_conj_apply)
  apply (subst (asm) wordle_output_local_reduce, blast, blast)
  apply (subst (asm) wordle_output_local_reduce, blast, blast)
  apply blast
  done


(* TODO: move *)

(* TODO: write examples: (1) Arthur's nointerference, (2) observing local state *)

lemma sepimp_conj_step_mp:
  \<open>p \<le> p' \<Longrightarrow> (p' \<midarrow>\<^emph>\<^sub>\<and> q) \<^emph>\<and> p \<le> q\<close>
  by (meson order_refl sepimp_conj_mono sepimp_conj_sepconj_conj_shunt)

lemma comp2_exch4_over_rel_times[simp]:
  fixes ra :: \<open>'a \<Rightarrow> 'a \<Rightarrow> bool\<close>
    and rb :: \<open>'b \<Rightarrow> 'b \<Rightarrow> bool\<close>
  shows \<open>((ra \<times>\<^sub>R rb) \<times>\<^sub>R (rc \<times>\<^sub>R rd)) \<circ>\<^sub>2 exch4 = ((ra \<times>\<^sub>R rc) \<times>\<^sub>R (rb \<times>\<^sub>R rd))\<close>
  by (force simp add: comp_rel_def exch4_def rel_times_def)

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
    \<open>R, G, I, F, \<top> \<turnstile> { p } c { q }\<close>
    \<open>\<forall>ra\<in>#all_atoms c. (\<forall>x x'. (I \<squnion> (I \<^emph>\<and> F)) x \<longrightarrow> ra x x' \<longrightarrow> {\<rho>. fst x \<rho> \<noteq> fst x' \<rho>} \<subseteq> V)\<close>
  shows
    \<open>liftR R, liftR G, \<bbbA>\<^sub>\<ddagger> f, \<lblot> F \<rblot>\<^sub>\<ddagger>, \<top> \<turnstile> { \<lblot> p \<rblot>\<^sub>\<ddagger> } liftC c { \<lblot> q \<rblot>\<^sub>\<ddagger> }\<close>
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


end