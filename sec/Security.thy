 theory Security
  imports SecLogic
begin

(* TODO: move *)

lemma subcomms_map_atom_distrib:
  \<open>subcomms (map_atom f c) = image_mset (map_atom f) (subcomms c)\<close>
  by (induct c) simp+

lemma comp2_surj_then_inj:
  \<open>surj f \<Longrightarrow> inj (\<lambda>a. a \<circ>\<^sub>2 f)\<close>
  apply (clarsimp simp add: surj_def inj_def comp2_def fun_eq_iff)
  apply metis
  done

lemma comp2_inj_then_surj:
  \<open>inj f \<Longrightarrow> surj (\<lambda>a. a \<circ>\<^sub>2 f)\<close>
  using choice[where Q=\<open>(\<lambda>(x,y) fx. Q x y fx) :: _ \<times> _ \<Rightarrow> _\<close> for Q, simplified]
  apply (fastforce simp add: surj_def inj_def comp2_def fun_eq_iff)
  done


section \<open> Proof Lifting to Paired-State Setting \<close>

subsection \<open> Helpers \<close>

text \<open> Note we use use the 'instantiation to exactly the frame' trick. \<close>
lemma framed_atom_unlift_helper:
  \<open>\<forall>f\<le>F. sp (unlift_rel\<^sub>\<ddagger> ara) (wssa R p \<^emph>\<and> f) \<le> q \<^emph>\<and> any_shared f \<Longrightarrow>
    All (quasirefl_preserv\<^sub>\<ddagger> ara) \<Longrightarrow>
    \<forall>f\<le>\<lblot> F \<rblot>\<^sub>\<ddagger>. sp ara (\<lblot> wssa R p \<rblot>\<^sub>\<ddagger> \<^emph>\<and> f) \<le> \<lblot> q \<rblot>\<^sub>\<ddagger> \<^emph>\<and> any_shared f\<close>
  unfolding quasirefl_preserv_exch4_def2 any_shared_def
  apply (clarsimp simp add: sepconj_conj_apply sp_apply le_fun_def)
  apply (rename_tac lfx' lfy' ssx' ssy' ssx ssy lsx lsy fx fy)
  apply (frule_tac x=\<open>(=) (fx, ssx)\<close> in spec, drule mp[of _ \<open>_ unlift_rel\<^sub>\<ddagger>\<close>])
   apply (simp add: le_fun_def lift_pred_exch4_def; fail)
  apply (drule_tac x=\<open>(=) (fy, ssy)\<close> in spec, drule mp[of _ \<open>_ unlift_rel\<^sub>\<ddagger>\<close>])
   apply (simp add: le_fun_def lift_pred_exch4_def; fail)
  apply (clarsimp simp add: sp_def le_fun_def sepconj_conj_apply imp_ex_conjL lift_pred_exch4_def
      unlift_rel_exch4_def2 imp_conjL)
  apply metis
  done

lemma atom_lift_guar_helper:
  \<open>rel_image snd (pretest (wssa R p \<^emph>\<and> F) \<sqinter> (ara \<circ>\<^sub>2 (exch4 \<circ> \<Delta>))) \<le> G \<Longrightarrow>
    All (quasirefl_preserv\<^sub>\<ddagger> ara) \<Longrightarrow>
    rel_image snd (pretest (\<lblot> wssa R p \<rblot>\<^sub>\<ddagger> \<^emph>\<and> \<lblot> F \<rblot>\<^sub>\<ddagger>) \<sqinter> ara) \<le> G \<times>\<^sub>R G\<close>
  apply (clarsimp simp add: le_fun_def sepconj_conj_apply imp_ex_conjL imp_conjL
      all_conj_distrib lift_pred_exch4_def quasirefl_preserv_exch4_def2)
  apply metis
  done

lemma cancellative'_lift_helper:
  \<open>cancellative' (\<Squnion> \<I>) (\<Squnion> \<I>) (sswa (\<Squnion> \<G>) F) \<Longrightarrow>
    cancellative'
      (\<Squnion> (lift_pred_exch4 ` \<I>))
      (\<Squnion> (lift_pred_exch4 ` \<I>))
      (sswa (\<Squnion>r\<in>\<G>. r \<times>\<^sub>R r) \<lblot> F \<rblot>\<^sub>\<ddagger>)\<close>
  apply (clarsimp simp add: cancellative'_def Bex_def lift_pred_exch4_def)
  apply (subgoal_tac \<open>sswa (\<Squnion>r\<in>\<G>. r \<times>\<^sub>R r) (\<lblot> F \<rblot> \<circ> exch4) \<le> sswa ((\<Squnion>\<G>) \<times>\<^sub>R (\<Squnion>\<G>)) (\<lblot> F \<rblot> \<circ> exch4)\<close>)
   prefer 2
   apply (meson SUP_least Sup_upper rel_times_mono sswa_rel_mono)
  apply (subgoal_tac \<open>sswa ((\<Squnion>\<G>) \<times>\<^sub>R (\<Squnion>\<G>)) (\<lblot> F \<rblot> \<circ> exch4) \<le> (\<lblot> sswa (\<Squnion>\<G>) F \<rblot> \<circ> exch4)\<close>)
   prefer 2
   apply (metis lift_pred_exch4_def sswa_lift_pred_exch4_semidistrib)
  apply (frule predicate1D[of \<open>sswa _ _\<close>, OF order.trans, rotated 2], assumption, assumption)
  apply auto
  done


subsection \<open> Main Lifting Theorem\<close>

(* TODO: Try to tighten up the qrefl side condition. *)
lemma genrgsep_proof_pairedst_lift:
  assumes
    \<open>R, G, I, F, T \<turnstile> { p } c { q }\<close>
    \<open>c = unlift_comm_exch4 cc\<close>
    \<open>\<top> \<le> all_atoms quasirefl_preserv\<^sub>\<ddagger> cc\<close>
    \<open>\<not> T RGSepDisj\<close>
  shows
    \<open>\<lblot> R \<rblot>\<^sub>R, \<lblot> G \<rblot>\<^sub>R, \<lblot> I \<rblot>\<^sub>\<ddagger>, \<lblot> F \<rblot>\<^sub>\<ddagger>, T \<squnion> (=) RGSepWeaken \<turnstile> { \<lblot> p \<rblot>\<^sub>\<ddagger> } cc { \<lblot> q \<rblot>\<^sub>\<ddagger> }\<close>
  using assms
proof (induct arbitrary: cc rule: rgsat.induct)
  case (rgsat_skip R p q I T G F)
  then show ?case
    apply (clarsimp simp add: unlift_comm_exch4_rev_iff simp del: sup_apply top_apply)
    apply (rule rgsat.rgsat_skip)
      apply (meson lift_pred_exch4_mono order.trans sswa_lift_pred_exch4_semidistrib; fail)
     apply (meson lift_pred_exch4_mono order.trans sswa_lift_pred_exch4_semidistrib; fail)
    apply force
    done
next
  case (rgsat_iter c R G i I F T p q)
  show ?case
    using rgsat_iter.prems rgsat_iter.hyps(3-)
    apply (clarsimp simp add: unlift_comm_exch4_rev_iff simp del: sup_apply top_apply)
    apply (rule rgsat.rgsat_iter[where i=\<open>\<lblot> i \<rblot>\<^sub>\<ddagger>\<close>])
       apply (rule rgsat_weaken[OF rgsat_iter.hyps(2) _ order.refl order.refl order.refl order.refl order.refl])
         apply blast
        apply (simp del: sup_apply; fail)
         apply (simp add: sswa_lift_pred_exch4_semidistrib; fail)
        apply (meson order.trans lift_pred_exch4_mono sswa_lift_pred_exch4_semidistrib; fail)
       apply fast
      apply (meson order.trans lift_pred_exch4_mono sswa_lift_pred_exch4_semidistrib; fail)
     apply (meson order.trans lift_pred_exch4_mono sswa_lift_pred_exch4_semidistrib; fail)
    apply force
    done
next
  case (rgsat_seq ca R G p px Ia F T cb q Ib I)
  show ?case
    using rgsat_seq.prems rgsat_seq.hyps(1,5-)
    apply (clarsimp simp add: unlift_comm_exch4_rev_iff simp del: sup_apply top_apply)
    apply (rule rgsat.rgsat_seq[where pp=\<open>\<lblot> px \<rblot>\<^sub>\<ddagger>\<close> and Ia=\<open>\<lblot> Ia \<rblot>\<^sub>\<ddagger>\<close> and Ib=\<open>\<lblot> Ib \<rblot>\<^sub>\<ddagger>\<close>])
        apply (rule rgsat_seq.hyps(2); force)
       apply (rule rgsat_seq.hyps(4); force)
      apply (meson order.trans lift_pred_exch4_mono sswa_lift_pred_exch4_semidistrib; fail)
     apply (meson order.trans lift_pred_exch4_mono sswa_lift_pred_exch4_semidistrib; fail)
    apply force
    done
next
  case (rgsat_indet ca R Ga p qa Ia F T cb Gb qb Ib G q I)
  show ?case
    using rgsat_indet.prems rgsat_indet.hyps(5-)
    apply (clarsimp simp add: unlift_comm_exch4_rev_iff simp del: sup_apply top_apply)
    apply (rule rgsat.rgsat_indet[where qa=\<open>\<lblot> qa \<rblot>\<^sub>\<ddagger>\<close> and qb=\<open>\<lblot> qb \<rblot>\<^sub>\<ddagger>\<close> and Ia=\<open>\<lblot> Ia \<rblot>\<^sub>\<ddagger>\<close> and Ib=\<open>\<lblot> Ib \<rblot>\<^sub>\<ddagger>\<close>])
            apply (rule rgsat_indet.hyps(2); force)
           apply (rule rgsat_indet.hyps(4); force)
          apply force
         apply force
        apply (meson order.trans lift_pred_exch4_mono sswa_lift_pred_exch4_semidistrib; fail)
       apply (meson order.trans lift_pred_exch4_mono sswa_lift_pred_exch4_semidistrib; fail)
      apply (meson order.trans lift_pred_exch4_mono sswa_lift_pred_exch4_semidistrib; fail)
     apply (meson order.trans lift_pred_exch4_mono sswa_lift_pred_exch4_semidistrib; fail)
    apply force
    done
next
  case (rgsat_endet ca R Ga p qa Ia F T cb Gb qb Ib G q I)
  show ?case
    using rgsat_endet.prems rgsat_endet.hyps(5-)
    apply (clarsimp simp add: unlift_comm_exch4_rev_iff simp del: sup_apply top_apply)
    apply (rule rgsat.rgsat_endet[where qa=\<open>\<lblot> qa \<rblot>\<^sub>\<ddagger>\<close> and qb=\<open>\<lblot> qb \<rblot>\<^sub>\<ddagger>\<close> and Ia=\<open>\<lblot> Ia \<rblot>\<^sub>\<ddagger>\<close> and Ib=\<open>\<lblot> Ib \<rblot>\<^sub>\<ddagger>\<close>])
            apply (rule rgsat_endet.hyps(2); force)
           apply (rule rgsat_endet.hyps(4); force)
          apply force
         apply force
        apply (meson order.trans lift_pred_exch4_mono sswa_lift_pred_exch4_semidistrib; fail)
       apply (meson order.trans lift_pred_exch4_mono sswa_lift_pred_exch4_semidistrib; fail)
      apply (meson order.trans lift_pred_exch4_mono sswa_lift_pred_exch4_semidistrib; fail)
     apply (meson order.trans lift_pred_exch4_mono sswa_lift_pred_exch4_semidistrib; fail)
    apply force
    done
next
  case (rgsat_par ca R Gb Ga pa qa Ia Ib F T cb pb qb G p q I)
  show ?case
    using rgsat_par.prems rgsat_par.hyps(5-)
    apply (clarsimp simp add: unlift_comm_exch4_rev_iff simp del: sup_apply top_apply)
    apply (rule rgsat.rgsat_par[where
          Ga=\<open>Ga \<times>\<^sub>R Ga\<close> and Gb=\<open>Gb \<times>\<^sub>R Gb\<close> and
          pa=\<open>\<lblot> pa \<rblot>\<^sub>\<ddagger>\<close> and pb=\<open>\<lblot> pb \<rblot>\<^sub>\<ddagger>\<close> and qa=\<open>\<lblot> qa \<rblot>\<^sub>\<ddagger>\<close> and qb=\<open>\<lblot> qb \<rblot>\<^sub>\<ddagger>\<close> and Ia=\<open>\<lblot> Ia \<rblot>\<^sub>\<ddagger>\<close> and Ib=\<open>\<lblot> Ib \<rblot>\<^sub>\<ddagger>\<close>])
           apply (rule rgsat_weaken[OF rgsat_par.hyps(2) order.refl order.refl _ order.refl order.refl])
                apply force
               apply force
              apply force
             apply force
           apply (simp add: lift_pred_exch4_sepconj_conj_distrib[symmetric] lift_pred_exch4_mono
        del: top_apply sup_apply; fail)
           apply force
          apply (rule rgsat_weaken[OF rgsat_par.hyps(4) order.refl order.refl _ order.refl order.refl])
               apply force
              apply force
             apply force
            apply force
           apply (simp add: lift_pred_exch4_sepconj_conj_distrib[symmetric] lift_pred_exch4_mono
        del: top_apply sup_apply; fail)
          apply force
         apply (metis rel_times_mono)
        apply (metis rel_times_mono)
       apply (metis lift_pred_exch4_mono lift_pred_exch4_sepconj_conj_distrib)
      apply (rule order.trans[OF _ lift_pred_exch4_mono, rotated], assumption)
      apply (simp add: lift_pred_exch4_sepconj_conj_distrib del: top_apply sup_apply)
      apply (meson sepconj_conj_mono sswa_sup_rel_lift_pred_exch4_semidistrib; fail)
     apply (rule order.trans[OF _ lift_pred_exch4_mono, rotated], assumption)
     apply (simp add: lift_pred_exch4_sepconj_conj_distrib del: top_apply sup_apply)
     apply (meson sepconj_conj_mono sswa_sup_rel_lift_pred_exch4_semidistrib; fail)
    apply force
    done
next
  case (rgsat_atom p' R p q q' F ar G I C)
  then show ?case
    apply (clarsimp simp add: unlift_comm_exch4_rev_iff inj_rel_image_inf_distrib[symmetric]
        simp del: sup_apply top_apply split_paired_All)
    apply (rule rgsat.rgsat_atom[where p=\<open>\<lblot> wssa R p \<rblot>\<^sub>\<ddagger>\<close> and q=\<open>\<lblot> sswa R q \<rblot>\<^sub>\<ddagger>\<close>])
      (* pre + post *)
          apply clarsimp
          apply (meson lift_pred_exch4_mono predicate1D; fail)
         apply clarsimp
         apply (meson lift_pred_exch4_mono predicate1D; fail)
      (* step condition *)
        apply (frule framed_atom_unlift_helper)
         apply fast
        apply clarsimp
        apply (frule spec, drule mp, assumption)
        apply (meson lift_pred_exch4_mono predicate1D sepconj_conj_monoL sswa_weaker; fail)
      (* guar *)
       apply (simp add: lift_pred_exch4_sepconj_conj_distrib[symmetric])
       apply (clarsimp simp del: split_paired_All simp add: le_fun_def lift_preds_exch4_apply
        unlift_rel_exch4_def2 imp_ex_conjL)
       apply (simp add: quasirefl_preserv_exch4_def2)
       apply (meson; fail)
      (* inv pre + post *)
      apply (simp add: lift_pred_exch4_mono; fail)
     apply (simp add: lift_pred_exch4_mono; fail)
      (* rules *)
    apply (simp; fail)
    done
next
  case (rgsat_frame c R G p q I F F' C)
  show ?case
    using rgsat_frame.prems rgsat_frame(3-)
    apply (simp add: lift_pred_exch4_sepconj_conj_distrib del: sup_apply top_apply)
    apply (rule rgsat_weaken[where p'=\<open>\<lblot> p \<rblot>\<^sub>\<ddagger> \<^emph>\<and> \<lblot> F' \<rblot>\<^sub>\<ddagger>\<close> and q'=\<open>\<lblot> q \<rblot>\<^sub>\<ddagger> \<^emph>\<and> \<lblot> F' \<rblot>\<^sub>\<ddagger>\<close>,
          OF _ _ _ order.refl order.refl order.refl order.refl])
       apply (rule rgsat.rgsat_frame)
         apply (rule rgsat_weaken[where F'=\<open> \<lblot> F \<^emph>\<and> F' \<rblot>\<^sub>\<ddagger>\<close>,
          OF _order.refl order.refl order.refl order.refl order.refl _])
           apply (cut_tac rgsat_frame.prems(2))
           apply (rule rgsat_frame.hyps(2); blast)
          apply (simp add: lift_pred_exch4_sepconj_conj_distrib[symmetric] lift_pred_exch4_mono
        sup.coboundedI1 del: sup_apply; fail)
         apply force
        apply (metis order_eq_iff sswa_sup_rel_lift_pred_exch4_semidistrib sswa_weaker)
       apply force
      apply force
     apply force
    apply force
    done
next
  case (rgsat_weaken c r' g' p' q' I' F' T p q r g I F)
  show ?case
    using rgsat_weaken.prems rgsat_weaken.hyps(3-)
    apply -
    apply (rule rgsat.rgsat_weaken[OF rgsat_weaken.hyps(2)])
             apply (simp add: lift_pred_exch4_mono; fail)
            apply force
           apply force
          apply (simp add: lift_pred_exch4_mono; fail)
         apply (simp add: lift_pred_exch4_mono; fail)
        apply force
       apply force
      apply (simp add: lift_pred_exch4_mono; fail)
     apply (simp add: lift_pred_exch4_mono; fail)
    apply force
    done
next
  case (rgsat_Disj p' P c R G q I F T)
  then show ?case
    by force \<comment> \<open> excluded \<close>
next
  case (rgsat_Conj \<I> I' \<G> G' Q q' c R p F C)
  then show ?case
    apply (clarsimp simp add: ball_conj_distrib simp del: top_apply sup_apply)
    apply (rule rgsat.rgsat_Conj[where
          \<I>=\<open>lift_pred_exch4 ` \<I>\<close> and \<G>=\<open>lift_rel ` \<G>\<close> and Q=\<open>lift_pred_exch4 ` Q\<close>])
            apply (metis lift_pred_exch4_Inf_distrib lift_pred_exch4_mono)
           apply (simp add: Inf_rel_times_distrib rel_times_mono; fail)
          apply (metis lift_pred_exch4_Inf_distrib lift_pred_exch4_mono)
         apply blast
        apply blast
       apply blast
      apply blast
     apply (simp add: cancellative'_lift_helper; fail)
    apply force
    done
qed


section \<open> Aligned Traces \<close>

subsection \<open> Execution Location \<close>

datatype loc =
  LHere |
  LParL loc | LParR loc |
  LEndetL loc | LEndetR loc |
  LIndetL | LIndetR |
  LLoopExit | LLoop loc

datatype 'a aact = ATau | AVis 'a

lemma map_aact_rev_iff[simp]:
  \<open>map_aact f \<alpha> = ATau \<longleftrightarrow> \<alpha> = ATau\<close>
  \<open>map_aact f \<alpha> = AVis fa \<longleftrightarrow> (\<exists>a. fa = f a \<and> \<alpha> = AVis a)\<close>
  by (cases \<alpha>; force)+

(* very simp-unsafe! *)
lemma All_loop_split:
  \<open>All p \<longleftrightarrow>
    p LHere \<and> (\<forall>l. p (LParL l)) \<and> (\<forall>l. p (LParR l)) \<and>
    (\<forall>l. p (LEndetL l)) \<and> (\<forall>l. p (LEndetR l)) \<and>
    p LIndetL \<and> p LIndetR \<and>
    p LLoopExit \<and> (\<forall>l. p (LLoop l))\<close>
  by (metis loc.exhaust)

lemma neq_all_avis_iff_eq_atau:
  \<open>(\<forall>a. \<alpha> \<noteq> AVis a) \<longleftrightarrow> \<alpha> = ATau\<close>
  by (case_tac \<alpha>) blast+

lemma neq_atau_iff_ex_eq_avis:
  \<open>\<alpha> \<noteq> ATau \<longleftrightarrow> (\<exists>a. \<alpha> = AVis a)\<close>
  by (case_tac \<alpha>) blast+


fun loc_leaf :: \<open>loc \<Rightarrow> loc\<close> where
  \<open>loc_leaf LHere = LHere\<close>
| \<open>loc_leaf (LParL l) = loc_leaf l\<close>
| \<open>loc_leaf (LParR l) = loc_leaf l\<close>
| \<open>loc_leaf (LEndetL l) = loc_leaf l\<close>
| \<open>loc_leaf (LEndetR l) = loc_leaf l\<close>
| \<open>loc_leaf LIndetL = LIndetL\<close>
| \<open>loc_leaf LIndetR = LIndetR\<close>
| \<open>loc_leaf LLoopExit = LLoopExit\<close>
| \<open>loc_leaf (LLoop l) = loc_leaf l\<close>

fun par_sched :: \<open>loc \<Rightarrow> loc\<close> where
  \<open>par_sched LHere = LHere\<close>
| \<open>par_sched (LParL l) = LParL (par_sched l)\<close>
| \<open>par_sched (LParR l) = LParR (par_sched l)\<close>
| \<open>par_sched (LEndetL l) = par_sched l\<close>
| \<open>par_sched (LEndetR l) = par_sched l\<close>
| \<open>par_sched LIndetL = LHere\<close>
| \<open>par_sched LIndetR = LHere\<close>
| \<open>par_sched LLoopExit = LHere\<close>
| \<open>par_sched (LLoop l) = par_sched l\<close>


subsection \<open> Extended Action \<close>

definition \<open>strip_aact \<alpha> \<equiv> if \<alpha> = ATau then Tau else Vis\<close>

lemma strip_aact_simps[simp]:
  \<open>strip_aact ATau = Tau\<close>
  \<open>strip_aact (AVis r) = Vis\<close>
  by (simp add: strip_aact_def)+

lemma strip_aact_rev_iff[simp]:
  \<open>strip_aact \<eta> = Tau \<longleftrightarrow> \<eta> = ATau\<close>
  \<open>strip_aact \<eta> = Vis \<longleftrightarrow> (\<exists>r. \<eta> = AVis r)\<close>
  by (simp add: strip_aact_def; meson aact.exhaust)+

lemmas strip_aact_rev_iff2 = strip_aact_rev_iff[THEN trans[OF eq_commute]]


subsection \<open> Parallel Opstep \<close>

text \<open>
  Unfortunately, because acts are often universally quantified,
  using a general type variable becomes prohibitively unwieldy.
  (Due to \<open>itself\<close> types and schematics type vars in \<open>induct\<close>.)
  Thus we just use unit.
\<close>
fun aopstep :: \<open>loc \<times> ('s \<Rightarrow> 's \<Rightarrow> bool) aact \<Rightarrow> 's pconfig \<Rightarrow> 's pconfig \<Rightarrow> bool\<close> where
  \<open>aopstep l\<alpha> (s, Skip) sc' \<longleftrightarrow> False\<close>
| \<open>aopstep l\<alpha> (s, ca ;; cb) sc' \<longleftrightarrow>
    l\<alpha> = (LHere, ATau) \<and> ca = Skip \<and> sc' = (s, cb) \<or>
    (\<exists>s' ca'. aopstep l\<alpha> (s, ca) (s', ca') \<and> sc' = (s', ca' ;; cb))\<close>
| \<open>aopstep l\<alpha> (s, ca \<^bold>\<sqinter> cb) sc' \<longleftrightarrow>
    l\<alpha> = (LIndetL, ATau) \<and> sc' = (s, ca) \<or>
    l\<alpha> = (LIndetR, ATau) \<and> sc' = (s, cb)\<close>
| \<open>aopstep l\<alpha> (s, ca \<^bold>\<box> cb) sc' \<longleftrightarrow>
    l\<alpha> = (LEndetL LHere, ATau) \<and> ca = Skip \<and> sc' = (s, cb) \<or>
    l\<alpha> = (LEndetR LHere, ATau) \<and> cb = Skip \<and> sc' = (s, ca) \<or>
    (\<exists>l\<alpha>' ca'.
      l\<alpha> = apfst LEndetL l\<alpha>' \<and> aopstep l\<alpha>' (s, ca) (fst sc', ca') \<and>
      snd sc' = (case snd l\<alpha>' of ATau \<Rightarrow> ca' \<^bold>\<box> cb | AVis _ \<Rightarrow> ca')) \<or>
    (\<exists>l\<alpha>' cb'.
      l\<alpha> = apfst LEndetR l\<alpha>' \<and> aopstep l\<alpha>' (s, cb) (fst sc', cb') \<and>
      snd sc' = (case snd l\<alpha>' of ATau \<Rightarrow> ca \<^bold>\<box> cb' | AVis _ \<Rightarrow> cb'))\<close>
| \<open>aopstep l\<alpha> (s, ca \<parallel> cb) sc' \<longleftrightarrow>
    l\<alpha> = (LHere, ATau) \<and> ca = Skip \<and> cb = Skip \<and> sc' = (s, Skip) \<or>
    (\<exists>l\<alpha>' s' ca'. l\<alpha> = apfst LParL l\<alpha>' \<and> aopstep l\<alpha>' (s, ca) (s', ca') \<and> sc' = (s', ca' \<parallel> cb)) \<or>
    (\<exists>l\<alpha>' s' cb'. l\<alpha> = apfst LParR l\<alpha>' \<and> aopstep l\<alpha>' (s, cb) (s', cb') \<and> sc' = (s', ca \<parallel> cb'))\<close>
| \<open>aopstep l\<alpha> (s, DO c OD) sc' \<longleftrightarrow>
    l\<alpha> = (LLoopExit, ATau) \<and> (\<forall>l\<alpha>' sc'. \<not> aopstep l\<alpha>' (s, c) sc') \<and> sc' = (s, Skip) \<or>
    (\<exists>l\<alpha>' s' c'. l\<alpha> = apfst LLoop l\<alpha>' \<and> aopstep l\<alpha>' (s, c) (s', c') \<and> sc' = (s', c' ;; DO c OD))\<close>
| \<open>aopstep l\<alpha> (s, \<langle>r\<rangle>) sc' \<longleftrightarrow>
    (l\<alpha> = (LHere, AVis r) \<and> r s (fst sc') \<and> snd sc' = Skip)\<close>

lemmas aopstep_induct = aopstep.induct[case_names Skip Seq Indet Endet Par DoLoop Atom]


paragraph \<open> Pretty parallel operational semantics \<close>

text \<open> \<open>sc\<close> can step to \<open>sc'\<close> \<close>
abbreviation pretty_aopstep :: \<open>_ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> _\<close> (\<open>_ \<midarrow>(_)\<rightarrow>\<^sub>a _\<close> [60,0,60] 60) where
  \<open>sc \<midarrow>l\<alpha>\<rightarrow>\<^sub>a sc' \<equiv> aopstep l\<alpha> sc sc'\<close>

text \<open> no steps from \<open>sc\<close> can take place \<close>
definition pretty_no_aopstep :: \<open>'s \<times> 's comm \<Rightarrow> bool\<close> (\<open>_ \<midarrow>'/\<rightarrow>\<^sub>a\<close> [60] 60) where
  \<open>sc \<midarrow>/\<rightarrow>\<^sub>a \<equiv> \<forall>l\<alpha> sc'. \<not> aopstep l\<alpha> sc sc'\<close>

abbreviation(input) ablocked (\<open>\<B>\<^sub>a\<close>) where
  \<open>\<B>\<^sub>a c \<equiv> \<lambda>s. (s, c) \<midarrow>/\<rightarrow>\<^sub>a\<close>


subsubsection \<open> Blocked Aopstep Lemmas \<close>

lemma aopstep_do_loop_iff[simp]:
  \<open>aopstep l\<alpha> (s, DO c OD) sc' \<longleftrightarrow>
    l\<alpha> = (LLoopExit, ATau) \<and> (s, c) \<midarrow>/\<rightarrow>\<^sub>a \<and> sc' = (s, Skip) \<or>
    (\<exists>l\<alpha>' s' c'. l\<alpha> = apfst LLoop l\<alpha>' \<and> aopstep l\<alpha>' (s, c) (s', c') \<and> sc' = (s', c' ;; DO c OD))\<close>
  by (simp add: pretty_no_aopstep_def)

declare aopstep.simps(6)[simp del]

lemma pretty_no_aopstep_simps[simp]:
  \<open>(s, Skip) \<midarrow>/\<rightarrow>\<^sub>a\<close>
  \<open>(s, ca ;; cb) \<midarrow>/\<rightarrow>\<^sub>a \<longleftrightarrow> ca \<noteq> Skip \<and> (s, ca) \<midarrow>/\<rightarrow>\<^sub>a\<close>
  \<open>(s, ca \<^bold>\<sqinter> cb) \<midarrow>/\<rightarrow>\<^sub>a \<longleftrightarrow> False\<close>
  \<open>(s, ca \<^bold>\<box> cb) \<midarrow>/\<rightarrow>\<^sub>a \<longleftrightarrow> ca \<noteq> Skip \<and> cb \<noteq> Skip \<and> (s, ca) \<midarrow>/\<rightarrow>\<^sub>a \<and> (s, cb) \<midarrow>/\<rightarrow>\<^sub>a\<close>
  \<open>(s, ca \<parallel> cb) \<midarrow>/\<rightarrow>\<^sub>a \<longleftrightarrow> (cb \<noteq> Skip \<or> ca \<noteq> Skip) \<and> (s, ca) \<midarrow>/\<rightarrow>\<^sub>a \<and> (s, cb) \<midarrow>/\<rightarrow>\<^sub>a\<close>
  \<open>(s, DO c OD) \<midarrow>/\<rightarrow>\<^sub>a \<longleftrightarrow> False\<close>
  \<open>(s, \<langle> ar \<rangle>) \<midarrow>/\<rightarrow>\<^sub>a \<longleftrightarrow> (\<nexists>s'. ar s s')\<close>
  by (clarsimp simp add: pretty_no_aopstep_def all_conj_distrib)+

lemma ablocked_map_atom_surj_eq[simp]:
  \<open>surj f \<Longrightarrow> \<B>\<^sub>a (map_atom (\<lambda>a. a \<circ>\<^sub>2 f) c) = \<B>\<^sub>a c \<circ> f\<close>
proof (induct c)
  case (Atomic x)
  then show ?case
    by simp (metis surjD)
qed (clarsimp simp add: fun_eq_iff)+
  

subsubsection \<open> Aopstep Lemmas \<close>

lemma aopstep_no_aopstep_contra:
  \<open>sc \<midarrow>l\<alpha>\<rightarrow>\<^sub>a sc' \<Longrightarrow> sc \<midarrow>/\<rightarrow>\<^sub>a \<Longrightarrow> False\<close>
  using pretty_no_aopstep_def by blast

lemma aopstep_iter_stepD:
  \<open>sc \<midarrow>l\<alpha>\<rightarrow>\<^sub>a sc' \<Longrightarrow>
    sc = (s, c) \<Longrightarrow>
    sc' = (s', c') \<Longrightarrow>
    (s, DO c OD) \<midarrow>apfst LLoop l\<alpha>\<rightarrow>\<^sub>a (s', c' ;; DO c OD)\<close>
  by clarsimp (metis apfst_conv surj_pair)

lemma aopstep_tau_preserves_state:
  \<open>sc \<midarrow>l\<alpha>\<rightarrow>\<^sub>a sc' \<Longrightarrow> snd l\<alpha> = ATau \<Longrightarrow> fst sc' = fst sc\<close>
  by (induct l\<alpha> sc sc' rule: aopstep_induct) fastforce+

lemma aopstep_vis_then_atom_step:
  \<open>sc \<midarrow>l\<alpha>\<rightarrow>\<^sub>a sc' \<Longrightarrow>
    snd l\<alpha> = AVis ar \<Longrightarrow>
    ar \<in># head_atoms (snd sc) \<and>
    ar (fst sc) (fst sc')\<close>
  by (induct l\<alpha> sc sc' rule: aopstep_induct; simp) fastforce+

lemma vis_aopstep_backwards_endet:
  \<open>sc \<midarrow>l\<alpha>\<rightarrow>\<^sub>a sc' \<Longrightarrow>
    snd l\<alpha> \<noteq> ATau \<Longrightarrow>
    snd sc' = ca' \<^bold>\<box> cb' \<Longrightarrow>
    \<exists>ca cb. snd sc = ca \<^bold>\<box> cb\<close>
  by (induct l\<alpha> sc sc' rule: aopstep_induct) fastforce+

lemma aopstep_then_aopstep_right_seqD:
  \<open>sc \<midarrow>l\<alpha>\<rightarrow>\<^sub>a sc' \<Longrightarrow>
    sc = (s, c) \<Longrightarrow>
    sc' = (s', c') \<Longrightarrow>
    (s, c ;; cx) \<midarrow>l\<alpha>\<rightarrow>\<^sub>a (s', c' ;; cx)\<close>
  by (induct l\<alpha> sc sc' rule: aopstep_induct) simp+

lemma aopstep_then_aopstep_right_endetD:
  \<open>sc \<midarrow>l\<alpha>\<rightarrow>\<^sub>a sc' \<Longrightarrow>
    sc = (s, c) \<Longrightarrow>
    sc' = (s', c') \<Longrightarrow>
    (snd l\<alpha> \<noteq> ATau \<longrightarrow> (s, c \<^bold>\<box> cb) \<midarrow>apfst LEndetL l\<alpha>\<rightarrow>\<^sub>a (s', c')) \<and>
    (snd l\<alpha> = ATau \<longrightarrow> (s, c \<^bold>\<box> cb) \<midarrow>apfst LEndetL l\<alpha>\<rightarrow>\<^sub>a (s', c' \<^bold>\<box> cb))\<close>
  by (clarsimp simp add: split_pairs split_pairs2)
    (metis aact.exhaust aact.simps(5) split_pairs2)

lemma aopstep_then_aopstep_left_endetD:
  \<open>sc \<midarrow>l\<alpha>\<rightarrow>\<^sub>a sc' \<Longrightarrow>
    sc = (s, c) \<Longrightarrow>
    sc' = (s', c') \<Longrightarrow>
    (snd l\<alpha> \<noteq> ATau \<longrightarrow> (s, ca \<^bold>\<box> c) \<midarrow>apfst LEndetR l\<alpha>\<rightarrow>\<^sub>a (s', c')) \<and>
    (snd l\<alpha> = ATau \<longrightarrow> (s, ca \<^bold>\<box> c) \<midarrow>apfst LEndetR l\<alpha>\<rightarrow>\<^sub>a (s', ca \<^bold>\<box> c'))\<close>
  by (clarsimp simp add: split_pairs split_pairs2)
    (metis aact.exhaust aact.simps(5) split_pairs2)

lemma aopstep_aact_cases:
  \<open>sc \<midarrow>l\<alpha>\<rightarrow>\<^sub>a sc' \<Longrightarrow>
    (\<And>r. sc \<midarrow>l\<alpha>\<rightarrow>\<^sub>a sc' \<Longrightarrow> snd l\<alpha> = AVis r \<Longrightarrow> r (fst sc) (fst sc') \<Longrightarrow> P) \<Longrightarrow>
    (sc \<midarrow>l\<alpha>\<rightarrow>\<^sub>a sc' \<Longrightarrow> snd l\<alpha> = ATau \<Longrightarrow> fst sc' = fst sc \<Longrightarrow> P) \<Longrightarrow>
    P\<close>
  using aopstep_tau_preserves_state aopstep_vis_then_atom_step
  by (cases \<open>snd l\<alpha>\<close>; blast)


subsubsection \<open> aopstep vs. opstep \<close>

lemma no_opstep_iff_no_aopstep:
  \<open>(s, c) \<midarrow>/\<rightarrow> \<longleftrightarrow> (s, c) \<midarrow>/\<rightarrow>\<^sub>a\<close>
  by (induct c) force+

lemma opstep_then_aopstep:
  \<open>sc \<midarrow>\<alpha>\<rightarrow> sc' \<Longrightarrow> \<exists>l \<eta>. strip_aact \<eta> = \<alpha> \<and> sc \<midarrow>(l, \<eta>)\<rightarrow>\<^sub>a sc'\<close>
proof (induct \<alpha> sc sc' rule: opstep_induct)
  case (Endet \<alpha> s ca cb sc')
  then show ?case
    apply (case_tac \<alpha>)
     apply clarsimp
     apply (metis split_pairs)
    apply clarsimp
    apply (metis aact.simps(5) surjective_pairing)
    done
next
  case (Par \<alpha> s ca cb sc')
  then show ?case
    by (simp, (elim disjE; clarsimp; metis))
next
  case (DoLoop \<alpha> s c sc')
  then show ?case
    using no_opstep_iff_no_aopstep[of s c]
    by (force simp add: pretty_no_aopstep_def)
qed force+

lemma aopstep_then_opstep:
  \<open>sc \<midarrow>l\<alpha>\<rightarrow>\<^sub>a sc' \<Longrightarrow> sc \<midarrow>strip_aact (snd l\<alpha>)\<rightarrow> sc'\<close>
proof (induct rule: aopstep_induct)
  case (Endet l\<alpha> s ca cb sc')
  then show ?case
    apply (cases \<open>snd l\<alpha>\<close>)
     apply clarsimp
     apply (metis aact.simps(4) split_pairs2 strip_aact_simps(1))
    apply clarsimp
    apply (metis aact.distinct(1) aact.simps(5) split_pairs2 strip_aact_def)
    done
next
  case (DoLoop l\<alpha> s c sc')
  then show ?case
    using opstep_then_aopstep
    apply (cases \<open>snd l\<alpha>\<close>; simp)
     apply (clarsimp simp add: pretty_no_aopstep_def split_pairs2)
     apply (metis opstep_then_aopstep pretty_no_opstep_def prod.collapse strip_aact_rev_iff2(1))
    apply fastforce
    done
qed force+


paragraph \<open> Aopstep Stable \<close>

definition
  \<open>astable_comm c \<equiv> \<lambda>s. \<forall>l sc'. \<not> (s, c) \<midarrow>(l, ATau)\<rightarrow>\<^sub>a sc'\<close>

lemma stable_comm_eq_astable_comm_eq:
  \<open>stable_comm c = astable_comm c\<close>
  unfolding stable_comm_def astable_comm_def fun_eq_iff
  by (induct c) (clarsimp simp add: all_conj_distrib no_opstep_iff_no_aopstep)+

lemma astable_comm_simps[simp]:
  \<open>astable_comm Skip = \<top>\<close>
  \<open>astable_comm (ca ;; cb) = (if ca \<noteq> Skip then astable_comm ca else \<bottom>)\<close>
  \<open>astable_comm (ca \<parallel> cb) = (if ca \<noteq> Skip \<or> cb \<noteq> Skip then astable_comm ca \<sqinter> astable_comm cb else \<bottom>)\<close>
  \<open>astable_comm (ca \<^bold>\<box> cb) = (if ca \<noteq> Skip \<and> cb \<noteq> Skip then astable_comm ca \<sqinter> astable_comm cb else \<bottom>)\<close>
  \<open>astable_comm (ca \<^bold>\<sqinter> cb) = \<bottom>\<close>
  \<open>astable_comm \<langle> a \<rangle> = \<top>\<close>
  \<open>astable_comm (DO ca OD) = vis_enabled_comm ca \<sqinter> astable_comm ca\<close>
  by (simp add: stable_comm_eq_astable_comm_eq[THEN sym])+


subsubsection \<open> interaction with subatom collectors \<close>

lemma aopstep_subcomm_atoms_mono:
  \<open>(s, c) \<midarrow>l\<alpha>\<rightarrow>\<^sub>a (s', c') \<Longrightarrow> set_mset (subcomm_atoms c') \<subseteq> set_mset (subcomm_atoms c)\<close>
  by (metis opstep_subcomm_atoms_set_mono aopstep_then_opstep)

lemma aopstep_preserves_all_atoms:
  \<open>(s, c) \<midarrow>l\<alpha>\<rightarrow>\<^sub>a (s', c') \<Longrightarrow> all_atoms p c \<le> all_atoms p c'\<close>
  by (meson aopstep_then_opstep opstep_preserves_all_atom_comm)

lemma aopstep_preserves_all_loops_all_head_atoms:
  \<open>(s, c) \<midarrow>l\<alpha>\<rightarrow>\<^sub>a (s', c') \<Longrightarrow> all_loops (all_head_atoms p) c \<le> all_loops (all_head_atoms p) c'\<close>
  by (meson aopstep_then_opstep opstep_preserves_all_loops_all_head_atoms)


subsubsection \<open> Aopstep lemmas \<close>

lemma aopstep_liftC_then_output_liftC:
  \<open>sc \<midarrow>l\<alpha>\<rightarrow>\<^sub>a sc' \<Longrightarrow>
    sc = (s, lift_comm_exch4 c) \<Longrightarrow>
    sc' = (s', cc') \<Longrightarrow>
    (\<exists>c'. cc' = lift_comm_exch4 c')\<close>
  by (meson aopstep_then_opstep opstep_preserves_map_atom)

lemma self_aopstep_impossible:
  \<open>(s, c) \<midarrow>l\<alpha>\<rightarrow>\<^sub>a (s', c) = False\<close>
  \<open>(s, c1) \<midarrow>l\<alpha>\<rightarrow>\<^sub>a (s', c1 \<^bold>\<box> c2) = False\<close>
  \<open>(s, c2) \<midarrow>l\<alpha>\<rightarrow>\<^sub>a (s', c1 \<^bold>\<box> c2) = False\<close>
  using self_opstep_impossible
  by (meson aopstep_then_opstep)+

lemma head_atomic_implies_all_aopstep_vis:
  \<open>sc \<midarrow>l\<alpha>\<rightarrow>\<^sub>a sc' \<Longrightarrow>
    head_atomic (snd sc) \<Longrightarrow>
    snd l\<alpha> \<noteq> ATau\<close>
  using head_atomic_implies_all_opstep_vis aopstep_then_opstep
  by (metis strip_aact_simps(1))

lemma head_atomic_then_any_head_guard_eq_not_ablocked:
  \<open>head_atomic c \<Longrightarrow> any_head_guard c = (\<lambda>s. \<not> (s, c) \<midarrow>/\<rightarrow>\<^sub>a)\<close>
  by (simp add: head_atomic_then_any_head_guard_eq_not_blocked no_opstep_iff_no_aopstep)

lemma pass_head_guard_then_some_vis_aopstep:
  \<open>any_head_guard c s \<Longrightarrow> \<exists>l\<alpha> sc'. (s, c) \<midarrow>l\<alpha>\<rightarrow>\<^sub>a sc' \<and> snd l\<alpha> \<noteq> ATau\<close>
  using opstep_then_aopstep pass_head_guard_then_some_vis_opstep by fastforce


subsection \<open> Branch Determinism \<close>

fun branch_determ :: \<open>('s \<times> 's) comm \<Rightarrow> 's \<times> 's \<Rightarrow> bool\<close> where
  \<open>branch_determ (ca \<^bold>\<box> cb) =
    (\<lambda>_. All (stable_comm (ca \<^bold>\<box> cb))) \<sqinter>
    - \<lblot> -(\<B>\<^sub>a ca \<circ> \<Delta>) \<bar> -(\<B>\<^sub>a cb \<circ> \<Delta>) \<rblot> \<sqinter>
    - \<lblot> -(\<B>\<^sub>a cb \<circ> \<Delta>) \<bar> -(\<B>\<^sub>a ca \<circ> \<Delta>) \<rblot>\<close>
| \<open>branch_determ (DO c OD) = \<bbbA> (\<B>\<^sub>a c \<circ> \<Delta>)\<close>
| \<open>branch_determ (ca \<^bold>\<sqinter> cb) = \<bottom>\<close>
| \<open>branch_determ c = \<top>\<close>

abbreviation \<open>all_branch_determ \<equiv> all_subcomms branch_determ\<close>
abbreviation \<open>all_head_branch_determ \<equiv> all_head_subcomms branch_determ\<close>


paragraph \<open> Branch Determinism Lemmas \<close>

lemma branch_determ_symp:
  \<open>symp (curry (branch_determ c))\<close>
  by (induct c) (force simp add: symp_def sec_agree_def)+

lemma aopstep_preserves_all_branch_determ:
  \<open>(s, c) \<midarrow>\<alpha>\<rightarrow>\<^sub>a (s', c') \<Longrightarrow> all_branch_determ c \<le> all_branch_determ c'\<close>
proof (induct c arbitrary: \<alpha> c')
  case (Endet c1 c2)
  then show ?case
    apply (clarsimp simp del: disj_not1 simp add: lift_pred_exch4_def
        stable_comm_eq_astable_comm_eq)
    apply (elim disjE[of \<open>\<alpha> = _ \<and> _\<close>])
         apply force
        apply force
    apply (clarsimp simp add: comp_def le_fun_def split_pairs2)
    apply (subgoal_tac \<open>snd \<alpha> \<noteq> ATau\<close>)
     prefer 2
     apply (metis astable_comm_def surj_pair)
    apply (metis aact.simps(5) neq_atau_iff_ex_eq_avis)
    done
qed fastforce+

lemma opstep_preserves_all_branch_determ:
  \<open>(s, c) \<midarrow>\<alpha>\<rightarrow> (s', c') \<Longrightarrow> all_branch_determ c \<le> all_branch_determ c'\<close>
  by (meson aopstep_preserves_all_branch_determ opstep_then_aopstep)


subsection \<open> Single-Double Step Relations \<close>

lemma lr_state_ablocked_then_lift_comm_ablocked:
  \<open>(sx, c) \<midarrow>/\<rightarrow>\<^sub>a \<Longrightarrow> ((sx, sy), lift_comm c) \<midarrow>/\<rightarrow>\<^sub>a\<close>
  \<open>(sy, c) \<midarrow>/\<rightarrow>\<^sub>a \<Longrightarrow> ((sx, sy), lift_comm c) \<midarrow>/\<rightarrow>\<^sub>a\<close>
  by (induct c) (force simp add: all_conj_distrib lift_rel_exch4_def)+

lemma branch_determ_implies_endet_reduces:
  assumes
    \<open>all_head_branch_determ (ca \<^bold>\<box> cb) (\<Delta> s)\<close>
    \<open>(\<Delta> s, ca \<^bold>\<box> cb) \<midarrow>l\<alpha>\<rightarrow>\<^sub>a (s', c')\<close>
  shows
    \<open>\<exists>a. snd l\<alpha> = AVis a\<close>
  using assms
  apply -
  apply (rule ccontr)
  apply (clarsimp simp add: comp_def split_pairs2 split: if_splits)
  apply (case_tac \<open>snd l\<alpha>\<close>; clarsimp)
  apply (metis aopstep_then_opstep snd_conv stable_comm_def strip_aact_simps(1))
  done


subsection \<open> The Key Lemmas \<close>

definition
  \<open>control_flow_determ c \<equiv> \<lambda>(sx,sy).
    all_head_branch_determ c (sx, sy) \<longrightarrow>
    (\<forall>ssx' l\<alpha>x cx'.
      (\<Delta> sx, c) \<midarrow>l\<alpha>x\<rightarrow>\<^sub>a (ssx', cx') \<longrightarrow>
    (\<forall>ssy' l\<alpha>y cy'.
      (\<Delta> sy, c) \<midarrow>l\<alpha>y\<rightarrow>\<^sub>a (ssy', cy') \<longrightarrow>
      par_sched (fst l\<alpha>x) = par_sched (fst l\<alpha>y) \<longrightarrow>
      snd l\<alpha>x = snd l\<alpha>y \<and> cy' = cx'))\<close>

lemma head_branch_determ_then_control_flow_determ_raw:
  assumes
    \<open>all_head_branch_determ c (sx, sy)\<close>
    \<open>(\<Delta> sx, c) \<midarrow>l\<alpha>x\<rightarrow>\<^sub>a (ssx', cx')\<close>
    \<open>(\<Delta> sy, c) \<midarrow>l\<alpha>y\<rightarrow>\<^sub>a (ssy', cy')\<close>
    \<open>par_sched (fst l\<alpha>x) = par_sched (fst l\<alpha>y)\<close>
  shows \<open>snd l\<alpha>x = snd l\<alpha>y \<and> cy' = cx'\<close>
  using assms
proof (induct c arbitrary: l\<alpha>x l\<alpha>y cx' cy')
  case (Endet c1 c2)
  then show ?case
    apply (clarsimp simp del: disj_not1 simp add: stable_comm_eq_astable_comm_eq astable_comm_def)
    apply (clarsimp simp add: split_pairs2)
    apply (subgoal_tac \<open>(\<exists>a. fst l\<alpha>x = LEndetL a) \<or> (\<exists>a. fst l\<alpha>x = LEndetR a)\<close>)
     prefer 2
     apply metis
    apply (subgoal_tac \<open>(\<exists>a. fst l\<alpha>y = LEndetL a) \<or> (\<exists>a. fst l\<alpha>y = LEndetR a)\<close>)
     prefer 2
     apply metis
    apply (elim disjE[of \<open>\<exists>a. fst _ = _ a\<close>]) (* 1 \<rightarrow> 4 *)
       apply (clarsimp simp add: comp_def, metis)
      apply (clarsimp simp add: comp_def, metis aopstep_no_aopstep_contra)
     apply (clarsimp simp add: comp_def, metis aopstep_no_aopstep_contra)
    apply (clarsimp simp add: comp_def, metis)
    done
next
  case (Iter c)
  then show ?case
    apply (clarsimp simp add: sec_agree_def)
    apply (elim disjE)
       apply force
      apply (blast dest: aopstep_no_aopstep_contra)
     apply (blast dest: aopstep_no_aopstep_contra)
    apply force
    done
qed fastforce+

lemma head_branch_determ_then_control_flow_determ:
  \<open>all_head_branch_determ c \<le> control_flow_determ c\<close>
  using head_branch_determ_then_control_flow_determ_raw
  by (clarsimp simp add: le_fun_def control_flow_determ_def)


subsection \<open> The Induced State-relation \<close>

definition \<open>induced_staterel c l\<alpha> \<equiv> \<lambda>s s'. \<exists>c'. (s, c) \<midarrow>l\<alpha>\<rightarrow>\<^sub>a (s', c')\<close>

lemma induced_staterel_vis_possibilities:
  \<open>induced_staterel c (l, AVis a) = \<bottom> \<or> induced_staterel c (l, AVis a) = a \<and> a \<in># head_atoms c\<close>
  unfolding induced_staterel_def
  by (induct c arbitrary: l)
    (clarsimp simp add: fun_eq_iff; metis)+

lemma induced_staterel_tau_subrel_eqrel:
  \<open>induced_staterel c (l, ATau) \<le> (=)\<close>
  unfolding induced_staterel_def
  by (induct c arbitrary: l) fastforce+

lemma induced_staterel_tau_nonrevealing_when:
  \<open>\<lblot> unlift_rel (induced_staterel c (l, ATau)) \<rblot>\<^sub>R s s' \<Longrightarrow>
    all_loops (\<lambda>ca. \<lblot> \<B>\<^sub>a ca \<circ> \<Delta> \<rblot> \<rightarrow> \<B>\<^sub>a ca) c s \<Longrightarrow>
    induced_staterel c (l, ATau) s s'\<close>
  unfolding induced_staterel_def
  apply (induct c arbitrary: l)
        apply force
       apply (clarsimp simp add: le_fun_def unlift_rel_def lift_rel_def)
       apply (case_tac \<open>c1 = Skip\<close>, force)
       apply blast
      apply (clarsimp simp add: fun_eq_iff unlift_rel_def lift_rel_def)
      apply (case_tac \<open>l = LHere\<close>, force)
      apply (case_tac \<open>\<exists>l'. l = LParL l'\<close>, force)
      apply (case_tac \<open>\<exists>l'. l = LParR l'\<close>, force)
      apply force
     apply (clarsimp simp add: fun_eq_iff unlift_rel_def lift_rel_def)
     apply (case_tac \<open>l = LIndetL\<close>, force)
     apply (case_tac \<open>l = LIndetR\<close>, force)
     apply force
    apply (clarsimp simp add: le_fun_def unlift_rel_def ex_disj_distrib lift_rel_def)
    apply (case_tac \<open>l = LEndetL LHere \<and> c1 = Skip\<close>)
     apply (simp; fail)
    apply (case_tac \<open>l = LEndetR LHere \<and> c2 = Skip\<close>)
     apply (simp; fail)
    apply (case_tac \<open>\<exists>l'. l = LEndetL l'\<close>)
       apply clarsimp
       apply (meson pretty_no_aopstep_def; fail)
    apply (case_tac \<open>\<exists>l'. l = LEndetR l'\<close>)
       apply clarsimp
     apply (meson pretty_no_aopstep_def; fail)
    apply force
   apply force
  apply (fastforce simp add: unlift_rel_def lift_rel_def)
  done

lemma induced_staterel_tau_quasirefl_preserv:
  \<open>all_head_loops (\<lambda>ca. \<B>\<^sub>a ca \<rightarrow> \<lblot> \<B>\<^sub>a ca \<circ> \<Delta> \<rblot>) c s \<Longrightarrow>
    quasirefl_preserv (induced_staterel c (l, ATau)) s\<close>
  unfolding quasirefl_preserv_eq induced_staterel_def
  apply clarsimp
  apply (induct c arbitrary: l)
        apply force
       apply (clarsimp simp add: le_fun_def unlift_rel_def lift_rel_def)
       apply (case_tac \<open>c1 = Skip\<close>, force)
       apply blast
      apply (clarsimp simp add: fun_eq_iff unlift_rel_def lift_rel_def)
      apply (case_tac \<open>l = LHere\<close>, force)
      apply (case_tac \<open>\<exists>l'. l = LParL l'\<close>, force)
      apply (case_tac \<open>\<exists>l'. l = LParR l'\<close>, force)
      apply force
     apply (clarsimp simp add: fun_eq_iff unlift_rel_def lift_rel_def)
     apply (case_tac \<open>l = LIndetL\<close>, force)
     apply (case_tac \<open>l = LIndetR\<close>, force)
     apply force
    apply (clarsimp simp add: le_fun_def unlift_rel_def ex_disj_distrib lift_rel_def)
    apply (case_tac \<open>l = LEndetL LHere \<and> c1 = Skip\<close>)
     apply (simp; fail)
    apply (case_tac \<open>l = LEndetR LHere \<and> c2 = Skip\<close>)
     apply (simp; fail)
    apply (case_tac \<open>\<exists>l'. l = LEndetL l'\<close>)
     apply (clarsimp, blast)
    apply (case_tac \<open>\<exists>l'. l = LEndetR l'\<close>)
     apply (clarsimp, blast)
    apply force
   apply force
  apply (fastforce simp add: unlift_rel_def lift_rel_def)
  done

lemma induced_staterel_tau_same_state_nonrevealing:
  \<open>r \<le> (=) \<Longrightarrow> same_state_nonrevealing r\<close>
  using predicate2D
  by (fastforce simp add: same_state_nonrevealing_iff induced_staterel_def)

lemma induced_staterel_tau_sym_preserv:
  \<open>all_head_loops (\<lambda>ca. symcl_states (\<B>\<^sub>a ca)) c s \<Longrightarrow>
    sym_preserv (induced_staterel c (l, ATau)) s\<close>
  unfolding sym_preserv_eq induced_staterel_def
  apply (induct c arbitrary: l)
        apply force
       apply (case_tac \<open>c1 = Skip\<close>, force)
       apply (simp; fail)
      apply (clarsimp simp add: fun_eq_iff unlift_rel_def lift_rel_def)
      apply (case_tac \<open>l = LHere\<close>, force)
      apply (case_tac \<open>\<exists>l'. l = LParL l'\<close>, force)
      apply (case_tac \<open>\<exists>l'. l = LParR l'\<close>, force)
      apply force
     apply (clarsimp simp add: fun_eq_iff unlift_rel_def lift_rel_def)
     apply (case_tac \<open>l = LIndetL\<close>, force)
     apply (case_tac \<open>l = LIndetR\<close>, force)
     apply force
    apply (clarsimp simp add: le_fun_def unlift_rel_def ex_disj_distrib lift_rel_def)
    apply (case_tac \<open>l = LEndetL LHere \<and> c1 = Skip\<close>, force)
    apply (case_tac \<open>l = LEndetR LHere \<and> c2 = Skip\<close>, force)
    apply (case_tac \<open>\<exists>l'. l = LEndetL l'\<close>, force)
    apply (case_tac \<open>\<exists>l'. l = LEndetR l'\<close>, force)
    apply force
   apply force
  apply (clarsimp simp add: fun_eq_iff unlift_rel_def lift_rel_def)
  apply (case_tac \<open>l = LLoopExit\<close>)
   apply clarsimp
   apply (metis (mono_tags, lifting) prod.case symcl_states_eq)
  apply blast
  done


section \<open> RGSep \<close>

subsection \<open> Translation Lemmas \<close>

lemma ablocking_then_map_atom_ablocking:
  \<open>(f s, c) \<midarrow>/\<rightarrow>\<^sub>a \<Longrightarrow> (s, map_atom (\<lambda>a. a \<circ>\<^sub>2 f) c) \<midarrow>/\<rightarrow>\<^sub>a\<close>
  by (induct c) (clarsimp simp add: map_atom_rev_iff)+

lemma surj_mapped_atom_ablocked_then_ablocked:
  \<open>surj f \<Longrightarrow> (s, map_atom (\<lambda>a. a \<circ>\<^sub>2 f) c) \<midarrow>/\<rightarrow>\<^sub>a \<Longrightarrow> (f s, c) \<midarrow>/\<rightarrow>\<^sub>a\<close>
  by (induct c) (simp; metis surj_def)+

lemma surj_mapped_atom_aopstep_then_aopstep:
  \<open>(s, map_atom (\<lambda>a. a \<circ>\<^sub>2 f) c) \<midarrow>apsnd (map_aact (\<lambda>a. a \<circ>\<^sub>2 f)) l\<alpha>\<rightarrow>\<^sub>a (s', map_atom (\<lambda>a. a \<circ>\<^sub>2 f) c') \<Longrightarrow>
    surj f \<Longrightarrow>
    (f s, c) \<midarrow>l\<alpha>\<rightarrow>\<^sub>a (f s', c')\<close>
proof (induct c arbitrary: l\<alpha> c')
  case (Seq c1 c2)
  show ?case
    using Seq.prems
    apply (clarsimp simp add: split_pairs2 map_atom_inj_eq_iff_eq[OF comp2_surj_then_inj]
        map_atom_rev_iff simp del: comp2_apply)
    apply (blast dest: Seq.hyps(1))
    done
next
  case (Par c1 c2)
  then show ?case
    apply (clarsimp simp add: split_pairs2 map_atom_inj_eq_iff_eq[OF comp2_surj_then_inj]
        map_atom_rev_iff simp del: comp2_apply)
    apply (subgoal_tac \<open>fst l\<alpha> = LHere \<or> (\<exists>a. fst l\<alpha> = LParL a) \<or> (\<exists>a. fst l\<alpha> = LParR a)\<close>)
     prefer 2
     apply blast
    apply (elim disjE[of \<open>fst l\<alpha> = _\<close>] disjE[of \<open>\<exists>a. fst l\<alpha> = _ a\<close>])
      apply (clarsimp; blast)+
    done
next
  case (Indet c1 c2)
  then show ?case
    by (clarsimp simp add: split_pairs2 map_atom_inj_eq_iff_eq[OF comp2_surj_then_inj]
        simp del: comp2_apply) blast
next
  case (Endet c1 c2)
  then show ?case
    apply (clarsimp simp add: split_pairs2 aact.case_distrib[where h=\<open>(=) _\<close>] simp del: comp2_apply)
    apply (subgoal_tac \<open>fst l\<alpha> = LHere \<or> (\<exists>a. fst l\<alpha> = LEndetL a) \<or> (\<exists>a. fst l\<alpha> = LEndetR a)\<close>)
     prefer 2
     apply blast
    apply (elim disjE[of \<open>fst l\<alpha> = _\<close>] disjE[of \<open>\<exists>a. fst l\<alpha> = _ a\<close>])
      apply (simp; fail)
     apply (clarsimp split: aact.splits simp add: map_atom_inj_eq_iff_eq[OF comp2_surj_then_inj]
        map_atom_rev_iff; fail)
    apply (clarsimp split: aact.splits simp add: map_atom_inj_eq_iff_eq[OF comp2_surj_then_inj]
        map_atom_rev_iff neq_all_avis_iff_eq_atau)
    apply (metis (lifting) map_aact_rev_iff(1))
    done
next
  case (Atomic a)
  then show ?case
    apply (clarsimp simp add: map_atom_rev_iff comp2_def fun_eq_iff split_pairs2)
    apply (metis surjE)
    done
next
  case (Iter c)
  then show ?case
    apply (clarsimp simp add: split_pairs2 simp del: comp2_apply)
    apply (case_tac \<open>c' = Skip\<close>)
     apply (force dest: surj_mapped_atom_ablocked_then_ablocked)
    apply (clarsimp simp add: map_atom_rev_iff map_atom_rev_iff2
        map_atom_inj_eq_iff_eq[OF comp2_surj_then_inj])
    apply blast
    done
qed (clarsimp simp add: map_atom_rev_iff)+

lemma inj_then_aopstep_then_map_aopstep:
  \<open>(f s, c) \<midarrow>l\<alpha>\<rightarrow>\<^sub>a (f s', c') \<Longrightarrow>
    inj f \<Longrightarrow>
    (s, map_atom (\<lambda>a. a \<circ>\<^sub>2 f) c) \<midarrow>apsnd (map_aact (\<lambda>a. a \<circ>\<^sub>2 f)) l\<alpha>\<rightarrow>\<^sub>a (s', map_atom (\<lambda>a. a \<circ>\<^sub>2 f) c')\<close>
proof (induct c arbitrary: l\<alpha> c')
  case (Endet c1 c2)
  then show ?case
    apply (clarsimp simp add: inj_eq split_pairs split_pairs2 simp del: comp2_apply)
    apply (elim disjE)
       apply fast
      apply fast
     apply (clarsimp simp add: aact.case_distrib split: aact.splits)
      apply (metis map_aact_rev_iff(1))
     apply fastforce
    apply (clarsimp simp add: aact.case_distrib split: aact.splits)
     apply (metis map_aact_rev_iff(1))
    apply fastforce
    done
next
  case (Iter c)
  then show ?case
    apply (clarsimp simp del: comp2_apply)
    apply (elim disjE)
     apply (simp add: inj_eq ablocking_then_map_atom_ablocking del: comp2_apply; fail)
    apply force
    done
qed (force simp add: inj_eq)+


subsection \<open> Misc Lemmas on Exch4 steps \<close>

\<comment> \<open> should be implied by the above switching lemmas \<close>
lemma either_ablocked_then_ablocked_together:
  \<open>(ax, c) \<midarrow>/\<rightarrow>\<^sub>a \<Longrightarrow> (\<ddagger> (ax, ay), lift_comm_exch4 c) \<midarrow>/\<rightarrow>\<^sub>a\<close>
  \<open>(ay, c) \<midarrow>/\<rightarrow>\<^sub>a \<Longrightarrow> (\<ddagger> (ax, ay), lift_comm_exch4 c) \<midarrow>/\<rightarrow>\<^sub>a\<close>
  by (induct c) (force simp add: all_conj_distrib lift_rel_exch4_def)+


subsection \<open> Exchanged Definitions \<close>

paragraph \<open> Branch Determ \<close>

definition branch_determ_exch4 (\<open>branch'_determ\<^sub>\<ddagger>\<close>) where
  \<open>branch_determ\<^sub>\<ddagger> c \<equiv> branch_determ (map_atom (\<lambda>a. a \<circ>\<^sub>2 \<ddagger>) c) \<circ> \<ddagger>\<close>

lemma branch_determ_exch4_simps[simp]:
  \<open>branch_determ\<^sub>\<ddagger> (ca \<^bold>\<box> cb) =
    (\<lambda>_. All (stable_comm (ca \<^bold>\<box> cb) \<circ> \<ddagger>)) \<sqinter>
    - \<lblot> -(\<B>\<^sub>a ca \<circ> \<ddagger> \<circ> \<Delta>) \<bar> -(\<B>\<^sub>a cb \<circ> \<ddagger> \<circ> \<Delta>) \<rblot>\<^sub>\<ddagger> \<sqinter>
    - \<lblot> -(\<B>\<^sub>a cb \<circ> \<ddagger> \<circ> \<Delta>) \<bar> -(\<B>\<^sub>a ca \<circ> \<ddagger> \<circ> \<Delta>) \<rblot>\<^sub>\<ddagger>\<close>
  \<open>branch_determ\<^sub>\<ddagger> (DO ca OD) = \<bbbA>\<^sub>\<ddagger> (\<B>\<^sub>a ca \<circ> \<ddagger> \<circ> \<Delta>)\<close>
  \<open>branch_determ\<^sub>\<ddagger> (ca \<^bold>\<sqinter> cb) = \<bottom>\<close>
  \<open>branch_determ\<^sub>\<ddagger> Skip = \<top>\<close>
  \<open>branch_determ\<^sub>\<ddagger> (ca ;; cb) = \<top>\<close>
  \<open>branch_determ\<^sub>\<ddagger> (ca \<parallel> cb) = \<top>\<close>
  \<open>branch_determ\<^sub>\<ddagger> (Atomic a) = \<top>\<close>
  by (simp add: branch_determ_exch4_def lift_preds_exch4_def sec_agree_exch4_def
      comp_inf_distrib comp_neg_distrib fun_eq_iff)+

lemma branch_determ_exch4_apply_exch4_eq[simp]:
  \<open>branch_determ\<^sub>\<ddagger> (map_atom (\<lambda>a. a \<circ>\<^sub>2 \<ddagger>) c) (\<ddagger> s) = branch_determ c s\<close>
  by (simp add: branch_determ_exch4_def comp_def)

lemma all_head_branch_determ_exch4_eq:
  \<open>all_head_subcomms branch_determ\<^sub>\<ddagger> c s = all_head_branch_determ (map_atom (\<lambda>a. a \<circ>\<^sub>2 \<ddagger>) c) (\<ddagger> s)\<close>
  by (induct c)
    (clarsimp simp del: comp2_apply simp add: lift_preds_exch4_def sec_agree_exch4_def)+

lemma all_branch_determ_exch4_eq:
  \<open>all_subcomms branch_determ\<^sub>\<ddagger> c = (all_branch_determ (map_atom (\<lambda>a. a \<circ>\<^sub>2 \<ddagger>) c) \<circ> \<ddagger>)\<close>
  by (induct c)
    (clarsimp simp del: comp2_apply simp add: lift_preds_exch4_def sec_agree_exch4_def)+

lemma aopstep_preserves_all_branch_determ_exch4:
  \<open>(s, c) \<midarrow>\<eta>\<rightarrow>\<^sub>a (s', c') \<Longrightarrow> all_subcomms branch_determ\<^sub>\<ddagger> c \<le> all_subcomms branch_determ\<^sub>\<ddagger> c'\<close>
  apply (subgoal_tac \<open>(\<exists>z. s = \<ddagger> z) \<and> (\<exists>z'. s' = \<ddagger> z')\<close>)
   prefer 2
   apply (metis exch4_idem)
  apply (elim exE conjE)
  apply simp
  apply (frule inj_then_aopstep_then_map_aopstep[of _ exch4])
   apply (simp; fail)
  apply (frule aopstep_preserves_all_branch_determ)
  apply (simp add: all_branch_determ_exch4_eq)
  done

lemma opstep_preserves_all_branch_determ_exch4:
  \<open>(s, c) \<midarrow>\<alpha>\<rightarrow> (s', c') \<Longrightarrow> all_subcomms branch_determ\<^sub>\<ddagger> c \<le> all_subcomms branch_determ\<^sub>\<ddagger> c'\<close>
  by (meson aopstep_preserves_all_branch_determ_exch4 opstep_then_aopstep)


paragraph \<open> Control Flow Determ \<close>

definition control_flow_determ_exch4 (\<open>control'_flow'_determ\<^sub>\<ddagger>\<close>) where
  \<open>control_flow_determ\<^sub>\<ddagger> c \<equiv> control_flow_determ (map_atom (\<lambda>a. a \<circ>\<^sub>2 \<ddagger>) c) \<circ> \<ddagger>\<close>

lemma control_flow_determ_exch4_apply_exch4[simp]:
  \<open>control_flow_determ\<^sub>\<ddagger> (map_atom (\<lambda>a. a \<circ>\<^sub>2 \<ddagger>) c) (\<ddagger> s) = control_flow_determ c s\<close>
  by (simp add: control_flow_determ_exch4_def comp_def)


subsection \<open> Key Lemmas \<close>

lemma head_branch_determ_exch4_then_control_flow_determ_exch4:
  \<open>all_head_subcomms branch_determ\<^sub>\<ddagger> c sxy \<Longrightarrow> control_flow_determ\<^sub>\<ddagger> c sxy\<close>
proof -
  assume assms2: \<open>all_head_subcomms branch_determ\<^sub>\<ddagger> c sxy\<close>
  then have \<open>all_head_subcomms branch_determ (map_atom (\<lambda>a. a \<circ>\<^sub>2 \<ddagger>) c) (\<ddagger> sxy)\<close>
    by (simp add: all_head_branch_determ_exch4_eq)
  then have \<open>control_flow_determ (map_atom (\<lambda>a. a \<circ>\<^sub>2 \<ddagger>) c) (\<ddagger> sxy)\<close>
    using head_branch_determ_then_control_flow_determ by blast
  then show ?thesis
    by (simp add: control_flow_determ_exch4_def)
qed


section \<open> Whole-program Information-Flow Security \<close>

\<comment> \<open>
  Very ugly, as we are assuming the security state view, rather than generic view,
  and jamming control_flow_determ in there too.
\<close>
inductive all_steps_exch4
  :: \<open>('s \<times> 's \<Rightarrow> 's \<times> 's \<Rightarrow> bool) \<Rightarrow>
      (('l, 's) rgsep_secstate \<Rightarrow> bool) \<Rightarrow>
      ((('l, 's) rgsep_secstate \<Rightarrow> ('l, 's) rgsep_secstate \<Rightarrow> bool) \<Rightarrow>
        (('l, 's) rgsep_secstate \<Rightarrow> bool)) \<Rightarrow>
      nat \<Rightarrow>
      ('l::pre_perm_alg, 's) rgsep_secstate comm \<Rightarrow>
      ('l, 's) rgsep_secstate \<Rightarrow>
      bool\<close>
  (\<open>all'_steps\<^sub>\<ddagger>\<close>)
  for R F stepp
  where all_steps_exch4I[intro]:
    \<open>(\<And>fs.
        fst s ## fs \<Longrightarrow>
        F (fs, snd s) \<Longrightarrow>
        (\<forall>l\<alpha>. stepp (induced_staterel c l\<alpha>) (fst s + fs, snd s)) \<and>
        control_flow_determ\<^sub>\<ddagger> c (fst s + fs, snd s)) \<Longrightarrow>
    (\<And>n' ss'. n = Suc n' \<Longrightarrow> R (snd s) ss' \<Longrightarrow> all_steps\<^sub>\<ddagger> R F stepp n' c (fst s, ss')) \<Longrightarrow>
    (\<And>n' fs \<alpha> lfs' ss' c'.
      n = Suc n' \<Longrightarrow>
      ((fst s + fs, snd s), c) \<midarrow>\<alpha>\<rightarrow> ((lfs', ss'), c') \<Longrightarrow>
      fst s ## fs \<Longrightarrow>
      F (fs, snd s) \<Longrightarrow>
      (\<exists>ls'. ls' ## fs \<and> lfs' = ls' + fs \<and> (\<alpha> = Tau \<longrightarrow> ls' = fst s) \<and>
        all_steps\<^sub>\<ddagger> R F stepp n' c' (ls', ss'))) \<Longrightarrow>
    all_steps\<^sub>\<ddagger> R F stepp n c s\<close>

theorem safety_and_branch_determ_and_all_atoms_implies_every_step:
  assumes noninduct:
    \<open>\<forall>r\<le>(=). I \<^emph>\<and> F \<le> stepp r\<close>
  assumes induct:
    \<open>safe R F G I q n c s\<close>
    \<open>I \<^emph>\<and> F \<le> all_subcomms branch_determ\<^sub>\<ddagger> c\<close>
    \<open>I \<^emph>\<and> F \<le> all_atoms stepp c\<close>
  shows
    \<open>all_steps\<^sub>\<ddagger> R F stepp n c s\<close>
  using induct
proof (induct rule: safe.induct)
  case (safeI c s n)

  obtain ls lsx lsy ss ssx ssy where s_eq:
    \<open>s = (ls, ss)\<close>
    \<open>ls = (lsx, lsy)\<close>
    \<open>ss = (ssx, ssy)\<close>
    by (metis surjective_pairing)
  note s_eq' = s_eq(1)[simplified s_eq(2-3)]

  {
    fix fs
    assume assms3:
      \<open>(lsx, lsy) ## fs\<close>
      \<open>F (fs, (ssx, ssy))\<close>

    have stateIF: \<open>(I \<^emph>\<and> F) ((lsx + fst fs, lsy + snd fs), (ssx, ssy))\<close>
      using assms3 s_eq' safeI.hyps(2)
      by (metis add_Pair sepconj_conj_apply split_pairs)

    have
      \<open>\<forall>l\<alpha>. stepp (induced_staterel c l\<alpha>) ((lsx, lsy) + fs, ssx, ssy)\<close>
      \<open>control_flow_determ\<^sub>\<ddagger> c (fst ((lsx, lsy), ssx, ssy) + fs, snd ((lsx, lsy), ssx, ssy))\<close>
    proof -
      have \<open>\<forall>r\<in>set_mset (head_atoms c). stepp r ((lsx, lsy) + fs, ssx, ssy)\<close>
        using safeI.prems all_atoms_then_holds_of_head_atom stateIF
        by fastforce
      then show \<open>\<forall>l\<alpha>. stepp (induced_staterel c l\<alpha>) ((lsx, lsy) + fs, ssx, ssy)\<close>
        using stateIF noninduct
        apply (clarsimp simp add: Ball_def)
        apply (rename_tac l \<alpha>)
        apply (case_tac \<alpha>)
         apply (meson induced_staterel_tau_subrel_eqrel predicate1D; fail)
        apply clarsimp
        apply (rename_tac r)
        apply (cut_tac c=c and l=l and a=r in induced_staterel_vis_possibilities)
        apply (elim disjE)
         apply clarsimp
         apply (meson order_bot_class.bot.extremum predicate1D; fail)
        apply clarsimp
        done

      have \<open>all_head_subcomms branch_determ\<^sub>\<ddagger> c (fst ((lsx, lsy), ssx, ssy) + fs, snd ((lsx, lsy), ssx, ssy))\<close>
        using all_subcomms_implies_all_head_subcomms safeI.prems(1) stateIF by fastforce
      then show \<open>control_flow_determ\<^sub>\<ddagger> c (fst ((lsx, lsy), ssx, ssy) + fs, snd ((lsx, lsy), ssx, ssy))\<close>
        using head_branch_determ_exch4_then_control_flow_determ_exch4 by fastforce
  qed
  } note secure_case = this

  show ?case
    using safeI.prems s_eq(1-3)
    apply simp
    apply (intro all_steps_exch4I[of _ _ _ _ n])
      apply (cut_tac ?fs2=fs in secure_case(1), force, force)
      apply (cut_tac ?fs2=fs in secure_case(2), force, force)
      apply force
     apply (frule safeI.hyps(4), force, force, force)
     apply blast
    apply (frule_tac fs=fs in safeI.hyps(5))
       apply (simp; fail)
      apply (simp; fail)
     apply (simp; fail)
    apply clarsimp
    apply (subgoal_tac \<open>I \<^emph>\<and> F \<le> all_atoms stepp c'\<close>)
     prefer 2
     apply (meson order.trans opstep_preserves_all_atom_comm_rev; fail)
    apply (subgoal_tac \<open>I \<^emph>\<and> F \<le> all_subcomms branch_determ\<^sub>\<ddagger> c'\<close>)
     prefer 2
     apply (meson opstep_preserves_all_branch_determ_exch4 order.trans; fail)
    apply (rule exI, rule conjI, assumption, rule exI, rule conjI, assumption,
        rule conjI[OF refl], rule conjI[OF refl])
    apply blast
    done
qed


lemma subrel_eqrel_then_secure_rel_eq[simp]:
  \<open>r \<le> (=) \<Longrightarrow> secure_rel r = \<top>\<close>
  apply (simp add: secure_rel_eq fun_eq_iff)
  apply (metis (full_types) predicate2D snd_conv)
  done

lemma subrel_eqrel_then_secure_rel_exch4_eq[simp]:
  \<open>r \<le> (=) \<Longrightarrow> secure_rel\<^sub>\<ddagger> r = \<top>\<close>
  by (simp add: secure_rel_exch4_def comp2_exch4_leq_shunt)

thm induced_staterel_tau_same_state_nonrevealing


subsection \<open> Security \<close>

abbreviation \<open>secure R F \<equiv> all_steps\<^sub>\<ddagger> R F secure_rel\<^sub>\<ddagger>\<close>

theorem safe_then_secure:
  assumes
    \<open>safe R F G I q n c s\<close>
    \<open>I \<^emph>\<and> F \<le> all_subcomms branch_determ\<^sub>\<ddagger> c\<close>
    \<open>I \<^emph>\<and> F \<le> all_atoms secure_rel\<^sub>\<ddagger> c\<close>
  shows
    \<open>secure R F n c s\<close>
  using assms
  by (simp add: safety_and_branch_determ_and_all_atoms_implies_every_step)


end