theory RGSep
  imports Semantics
begin

section \<open> Algebraic Rely-Guarantee \<close>

subsection \<open> Sup Algebra \<close>

typedef 'a sup_jalg = \<open>UNIV :: 'a set\<close> ..

setup_lifting type_definition_sup_jalg


instantiation sup_jalg :: (sup) join
begin
lift_definition join_sup_jalg :: \<open>'a sup_jalg \<Rightarrow> 'a sup_jalg \<Rightarrow> 'a sup_jalg \<Rightarrow> bool\<close> is
  \<open>\<lambda>a b c. c = a \<squnion> b\<close> .
instance ..
end

instance sup_jalg :: (semilattice_sup) join_alg
  apply standard
   apply (transfer, simp add: sup.assoc; fail)
  apply (transfer, simp add: sup.commute; fail)
  done

instance sup_jalg :: (semilattice_sup) join_positive
  apply standard
  apply (transfer, simp add: join_sup_jalg_def, metis sup_antisym)
  done

instance sup_jalg :: (semilattice_sup) join_functional
  by standard (transfer, simp add: join_sup_jalg_def)

(* not join_cancel *)
(* not join_nounit *)

instantiation sup_jalg :: (\<open>{semilattice_sup, order_bot}\<close>) join_unitof
begin
lift_definition join_unitof_sup_jalg :: \<open>'a sup_jalg \<Rightarrow> 'a sup_jalg\<close> is
  \<open>\<lambda>_. \<bottom>\<close> .
instance ..
end

instance sup_jalg :: (bounded_semilattice_sup_bot) join_munital
  by standard
    (transfer, simp add: join_unitof_sup_jalg_def join_sup_jalg_def)

instantiation sup_jalg :: (\<open>{semilattice_sup, order_bot}\<close>) join_unit
begin
lift_definition join_unit_sup_jalg :: \<open>'a sup_jalg\<close> is \<open>\<bottom>\<close> .
instance ..
end

instance sup_jalg :: (bounded_semilattice_sup_bot) join_unital
  by standard
    (transfer, simp add: join_unit_sup_jalg_def join_sup_jalg_def)


paragraph \<open> lifting instances \<close>

instantiation sup_jalg :: (ord) ord
begin
lift_definition less_eq_sup_jalg :: \<open>'a sup_jalg \<Rightarrow> 'a sup_jalg \<Rightarrow> bool\<close> is \<open>(\<le>)\<close> .
lift_definition less_sup_jalg :: \<open>'a sup_jalg \<Rightarrow> 'a sup_jalg \<Rightarrow> bool\<close> is \<open>(<)\<close> .
instance ..
end

instance sup_jalg :: (preorder) preorder
  apply standard
    apply (transfer, metis less_le_not_le)
   apply (transfer, metis order.refl)
  apply (transfer, metis order.trans)
  done

instance sup_jalg :: (order) order
  by standard (transfer, force)

instantiation sup_jalg :: (sup) sup
begin
lift_definition sup_sup_jalg :: \<open>'a sup_jalg \<Rightarrow> 'a sup_jalg \<Rightarrow> 'a sup_jalg\<close> is \<open>(\<squnion>)\<close> .
instance ..
end

instance sup_jalg :: (semilattice_sup) semilattice_sup
  by standard (transfer, clarsimp)+

instantiation sup_jalg :: (bot) bot
begin
lift_definition bot_sup_jalg :: \<open>'a sup_jalg\<close> is \<open>bot\<close> .
instance ..
end

instance sup_jalg :: (order_bot) order_bot
  by standard (transfer, simp)


subsection \<open> Stabilised Set \<close>

typedef 'a rgst =
  \<open>{(P::'a \<Rightarrow> bool, R::'a \<Rightarrow> 'a \<Rightarrow> bool, G::'a \<Rightarrow> 'a \<Rightarrow> bool).
    reflp R \<and> transp R \<and> reflp G \<and> transp G \<and> sp R P \<le> P}\<close>
  by (rule_tac x=\<open>(\<top>, (=), (=))\<close> in exI) simp

setup_lifting type_definition_rgst

lift_definition mk_rgst :: \<open>('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> 'a rgst\<close> is
  \<open>\<lambda>R G P. (sp R\<^sup>*\<^sup>* P, R\<^sup>*\<^sup>*, G\<^sup>*\<^sup>*)\<close>
  by (simp add: sp_relcomp)

lift_definition rgst_rely :: \<open>'a rgst \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool)\<close> is \<open>fst \<circ> snd\<close> .
lift_definition rgst_guar :: \<open>'a rgst \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool)\<close> is \<open>snd \<circ> snd\<close> .
lift_definition rgst_states :: \<open>'a rgst \<Rightarrow> ('a \<Rightarrow> bool)\<close> is fst .

lemma tranclp_sup_under_tranclp_eq[simp]:
  \<open>(a\<^sup>+\<^sup>+ \<squnion> b)\<^sup>+\<^sup>+ = (a \<squnion> b)\<^sup>+\<^sup>+\<close>
  apply (clarsimp simp add: fun_eq_iff)
  apply (rule iffI)
   apply (rule tranclp_trans_induct[of \<open>a\<^sup>+\<^sup>+ \<squnion> b\<close> _ _ \<open>(a \<squnion> b)\<^sup>+\<^sup>+\<close>])
     apply force
    apply (metis predicate2D subrel_sup_tranclp(1-2) sup2E tranclp.r_into_trancl)
   apply force
  apply (rule tranclp_trans_induct[of \<open>a \<squnion> b\<close> _ _ \<open>(a\<^sup>+\<^sup>+ \<squnion> b)\<^sup>+\<^sup>+\<close>])
    apply force
   apply (metis predicate2D subrel_sup_tranclp(1-2) sup2E tranclp.r_into_trancl)
  apply force
  done

lemma sup_tranclp_under_tranclp_eq[simp]:
  \<open>(a \<squnion> b\<^sup>+\<^sup>+)\<^sup>+\<^sup>+ = (a \<squnion> b)\<^sup>+\<^sup>+\<close>
  apply (clarsimp simp add: fun_eq_iff)
  apply (rule iffI)
   apply (rule tranclp_trans_induct[of \<open>a \<squnion> b\<^sup>+\<^sup>+\<close> _ _ \<open>(a \<squnion> b)\<^sup>+\<^sup>+\<close>])
     apply force
    apply (metis predicate2D subrel_sup_tranclp(1-2) sup2E tranclp.r_into_trancl)
   apply force
  apply (rule tranclp_trans_induct[of \<open>a \<squnion> b\<close> _ _ \<open>(a \<squnion> b\<^sup>+\<^sup>+)\<^sup>+\<^sup>+\<close>])
    apply force
   apply (metis predicate2D subrel_sup_tranclp(1-2) sup2E tranclp.r_into_trancl)
  apply force
  done


instantiation rgst :: (type) join
begin
lift_definition join_rgst :: \<open>'a rgst \<Rightarrow> 'a rgst \<Rightarrow> 'a rgst \<Rightarrow> bool\<close> is
  \<open>\<lambda>(pa, Ra, Ga) (pb, Rb, Gb) (pc, Rc, Gc).
      Rc = Ra \<sqinter> Rb \<and> (Ga \<squnion> Gb)\<^sup>+\<^sup>+ = Gc \<and> Ga \<le> Rb \<and> Gb \<le> Ra \<and> pc = pa \<and> pc = pb\<close> .
instance ..
end

instance rgst :: (type) join_alg
  apply standard
   apply (transfer, clarsimp simp add: inf.assoc[symmetric] sup.assoc[symmetric])
  sorry
  apply (transfer, clarsimp)
  done

instance rgst :: (type) join_positive
  by standard
    (transfer, clarsimp)

(* not join_functional *)
(* not join_cancel *)
(* not join_nounit *)

instantiation rgst :: (type) join_unitof
begin
lift_definition join_unitof_rgst :: \<open>'a rgst \<Rightarrow> 'a rgst\<close> is
  \<open>\<lambda>(P, R). (P, R)\<close>
  by clarsimp
instance ..
end

instance rgst :: (type) join_munital
  by standard
    (transfer, clarsimp)

instantiation rgst :: (type) join_unit
begin
lift_definition join_unit_rgst :: \<open>'a rgst\<close> is
  \<open>(\<bottom>, (=))\<close>
  by clarsimp
instance ..
end

(* no join_unital *)


section \<open> RGSep \<close>

abbreviation \<open>sswa r \<equiv> sp ((=) \<times>\<^sub>R r\<^sup>*\<^sup>*)\<close>
abbreviation \<open>wssa r \<equiv> wlp ((=) \<times>\<^sub>R r\<^sup>*\<^sup>*)\<close>

lemmas relyrel_trans = rel_times_trans[OF transp_equality transp_rtranclp]
lemmas relyrel_mono = rel_times_mono[OF order.refl rtranclp_mono]


type_synonym ('a, 'b) rgsep_st = \<open>'a \<times> (('b \<Rightarrow> 'b \<Rightarrow> bool) sup_jalg \<times> 'b rgst)\<close>

abbreviation local_pred
  :: \<open>('a \<Rightarrow> bool) \<Rightarrow> ('a, 'b) rgsep_st \<Rightarrow> bool\<close> (\<open>\<L>\<close>)
  where
    \<open>\<L> p \<equiv> p \<circ> fst\<close>

abbreviation shared_pred
  :: \<open>('b \<Rightarrow> bool) \<Rightarrow> ('a, 'b) rgsep_st \<Rightarrow> bool\<close> (\<open>\<S>\<close>)
  where
    \<open>\<S> p \<equiv> ((\<le>) p) \<circ> rgst_states \<circ> snd \<circ> snd\<close>

lift_definition mk_rgsep_alg_precond_lift
  :: \<open>('s \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow>
        ('s \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow>
        ('l \<times> 's \<Rightarrow> bool) \<Rightarrow>
        (('l, 's) rgsep_st \<Rightarrow> bool)\<close>
  is
    \<open>\<lambda>R G p (ls, (G', (S', R'))). p \<le> ((=) ls) \<times>\<^sub>P S' \<and> R \<le> R' \<and> G' \<le> G\<close> .

lift_definition mk_rgsep_alg_postcond_lift
  :: \<open>('s \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow>
        ('s \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow>
        ('l \<times> 's \<Rightarrow> bool) \<Rightarrow>
        (('l, 's) rgsep_st \<Rightarrow> bool)\<close>
  is
    \<open>\<lambda>R G q (ls, (G', (S', R'))). ((=) ls) \<times>\<^sub>P S' \<le> q \<and> R \<le> R' \<and> G' \<le> G\<close> .

lift_definition mk_rgsep_alg_atomrel
  :: \<open>('s \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow>
        ('s \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow>
        ('l \<times> 's \<Rightarrow> 'l \<times> 's \<Rightarrow> bool) \<Rightarrow>
        (('l, 's) rgsep_st \<Rightarrow> ('l, 's) rgsep_st \<Rightarrow> bool)\<close>
  is
    \<open>\<lambda>Rx Gx ar (ls, (G, (P, R))) (ls', (G', (Q', R'))).
      (\<exists>Q. sp ar ((=) ls \<times>\<^sub>P P) \<le> (=) ls' \<times>\<^sub>P Q \<and> Q' = sp R Q) \<and>
      R' = R \<and>
      G' = G\<close> .


definition rgsep_semsat
  :: \<open>('s \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow>
      ('s \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow>
      ('l::join_alg \<times> 's \<Rightarrow> bool) \<Rightarrow>
      ('l \<times> 's \<Rightarrow> bool) \<Rightarrow>
      ('l \<times> 's \<Rightarrow> bool) \<Rightarrow>
      ('l \<times> 's) comm \<Rightarrow>
      ('l \<times> 's \<Rightarrow> bool) \<Rightarrow>
      bool\<close>
  (\<open>_, _, _, _ \<Turnstile> { _ } _ { _ }\<close> [50,0,0,0,0,0,50] 50) where
  \<open>R, G, F, I \<Turnstile> { p } c { q } \<equiv>
    mk_rgsep_alg_postcond_lift R G F,
    mk_rgsep_alg_precond_lift R G I \<Turnstile>
    { mk_rgsep_alg_precond_lift R G p }
      map_atom (mk_rgsep_alg_atomrel R G) c
    { mk_rgsep_alg_postcond_lift R G q }\<close>

lemma mk_rgsep_alg_pred_sswa_eq:
  \<open>R \<le> R' \<Longrightarrow> mk_rgsep_alg_postcond_lift G R (sswa R p) \<le> mk_rgsep_alg_postcond_lift R G p\<close>
  apply (clarsimp simp add: fun_eq_iff le_fun_def)
  apply transfer
  apply clarsimp
  oops

lemma mk_rgsep_alg_pred_sepconj_distrib:
  \<open>mk_rgsep_alg_precond_lift G R (p \<^emph> q) =
    mk_rgsep_alg_precond_lift G R p \<^emph> mk_rgsep_alg_precond_lift G R q\<close>
  apply (clarsimp simp add: fun_eq_iff sepconj_def)
  apply transfer
  apply (clarsimp simp add: le_fun_def)
  apply (intro iffI)
   prefer 2
   apply clarsimp
  sledgehammer
  sorry


lemma rgsep_par:
  \<open>(R \<squnion> Gb), Ga, (Ib \<^emph> F), Ia \<Turnstile> { pa } ca { qa } \<Longrightarrow>
    (R \<squnion> Ga), Gb, (Ia \<^emph> F), Ib \<Turnstile> { pb } cb { qb } \<Longrightarrow>
    R, (Ga \<squnion> Gb), F, (sswa (R \<squnion> Gb) Ia \<^emph> sswa (R \<squnion> Ga) Ib) \<Turnstile>
      { pa \<^emph> pb } ca \<parallel> cb { sswa (R \<squnion> Gb) qa \<^emph> sswa (R \<squnion> Ga) qb }\<close>

  apply (simp add: mk_rgsep_alg_pred_sepconj_distrib)
  apply (rule semsat_weaken)
  apply (rule semsat_par)

end