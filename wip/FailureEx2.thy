theory FailureEx2
  imports "../Soundness"
begin


text \<open>
  In (TODO: cite) Bannister and Höfner introduce the positive-negative heap model.
  This provides a model of resourceful failure that, when a command lacks a resource,
  records that lack in the 'negative heap'. This negative heap stores memory cells which
  have failed to be present when requested. This model has several nice logical properties,
  including the fact it can be used for forward reasoning.
\<close>

section \<open> Separated Pairs \<close>

typedef(overloaded) ('a::pre_multiunit_sep_alg) seppair = \<open>{(a,b)|a b::'a. a ## b}\<close>
  by blast
setup_lifting seppair.type_definition_seppair


instantiation seppair :: (pre_multiunit_sep_alg) disjoint
begin
lift_definition disjoint_seppair :: \<open>'a seppair \<Rightarrow> 'a seppair \<Rightarrow> bool\<close> is
  \<open>\<lambda>(a::'a,na::'a) (b,nb). a ## b \<and> a ## nb \<and> na ## b \<and> na ## nb\<close> .
instance by standard
end

instantiation seppair :: (\<open>{pre_multiunit_sep_alg, disjoint_parts_pre_perm_alg}\<close>) plus
begin
lift_definition plus_seppair :: \<open>'a seppair \<Rightarrow> 'a seppair \<Rightarrow> 'a seppair\<close> is
  \<open>\<lambda>(a::'a,na::'a) (b,nb).
    if a ## b \<and> a ## nb \<and> na ## b \<and> na ## nb
      then (a + b, na + nb)
      else \<comment> \<open>impossible\<close> (a,na)\<close>
  by (clarsimp simp add: disjoint_sym_iff)
instance by standard
end

instance seppair :: (\<open>{pre_multiunit_sep_alg, disjoint_parts_pre_perm_alg}\<close>) pre_perm_alg
  apply standard
      apply (transfer, (clarsimp simp add: partial_add_assoc; fail))
     apply (transfer, (clarsimp simp add: disjoint_sym_iff partial_add_commute; fail))
    apply (transfer, (clarsimp simp add: disjoint_sym_iff; fail))
   apply (transfer, (clarsimp; fail))
  apply (transfer, (simp add: case_prod_beta; metis disjoint_sym_iff))
  done

instance seppair :: (\<open>{multiunit_sep_alg, disjoint_parts_pre_perm_alg}\<close>) positivity_law
  by standard
    (transfer, clarsimp, metis disjointness_left_plus_eq unit_sub_closure2')

instantiation seppair :: (\<open>{pre_multiunit_sep_alg, disjoint_parts_pre_perm_alg}\<close>) pre_multiunit_sep_alg
begin
lift_definition unitof_seppair :: \<open>'a seppair \<Rightarrow> 'a seppair\<close> is
  \<open>\<lambda>(x, y). (unitof x, unitof y)\<close>
  by (clarsimp simp add: disjoint_same_unit sepadd_unit_selfsep unitof_is_sepadd_unit)
instance
  apply standard
   apply (transfer, clarsimp, metis disjoint_same_unit unitof_disjoint)
  apply (transfer, clarsimp)
  done
end

instance seppair :: (\<open>{multiunit_sep_alg, disjoint_parts_pre_perm_alg}\<close>) multiunit_sep_alg
  by standard
    (transfer, clarsimp, metis disjointness_left_plus_eq unit_sub_closure2')

instantiation seppair :: (\<open>{pre_sep_alg, disjoint_parts_pre_perm_alg}\<close>) zero
begin
lift_definition zero_seppair :: \<open>'a seppair\<close> is \<open>(0, 0)\<close> by force
instance by standard
end

instance seppair :: (\<open>{pre_sep_alg, disjoint_parts_pre_perm_alg}\<close>) pre_sep_alg
  by standard (transfer, force)+


paragraph \<open> Special Laws \<close>

instance seppair :: (\<open>{pre_multiunit_sep_alg, disjoint_parts_pre_perm_alg}\<close>) disjoint_parts_pre_perm_alg
  by standard (transfer, clarsimp)

instance seppair :: (\<open>{pre_multiunit_sep_alg,disjoint_parts_pre_perm_alg,strong_sep_pre_perm_alg}\<close>)
  strong_sep_pre_perm_alg
  apply standard
  apply (simp add: sepadd_unit_def)
  apply transfer
  apply clarsimp
  apply (metis selfsep_iff sepadd_unitE)
  done

instance seppair :: (\<open>{trivial_selfdisjoint_pre_perm_alg,pre_multiunit_sep_alg,
  disjoint_parts_pre_perm_alg}\<close>)
  trivial_selfdisjoint_pre_perm_alg
  by standard (transfer, clarsimp, simp add: selfdisjoint_same)

instance seppair :: (\<open>{crosssplit_pre_perm_alg,pre_multiunit_sep_alg,disjoint_parts_pre_perm_alg}\<close>)
  crosssplit_pre_perm_alg
  apply standard
  apply transfer
  apply clarsimp
  apply (drule cross_split[rotated 2], blast, blast)
  apply (drule cross_split[rotated 2], blast, blast)
  apply (clarsimp simp del: ex_simps simp add: ex_simps[symmetric])
  apply (simp only: imp_conjR[where Q=\<open>_ \<longrightarrow> _\<close> and R=\<open>_ \<longrightarrow> _\<close>] conj.assoc)
  apply (rename_tac pax nax pbx nbx pay nay pby nby)
  apply (rule_tac x=pax in exI)
  apply (rule_tac x=nax in exI)
  apply (rule_tac x=pbx in exI)
  apply (rule_tac x=nbx in exI)
  apply (clarsimp simp del: ex_simps)
  apply (rule_tac x=pay in exI)
  apply (rule_tac x=nay in exI)
  apply (clarsimp simp del: ex_simps)
  apply (rule_tac x=pby in exI)
  apply (rule_tac x=nby in exI)
  apply clarsimp
  done

text \<open>
  The option-instance is only cancellable when the sub-instance is cancellative *and*
  that instance has no units.
\<close>
instance seppair :: (\<open>{cancel_pre_perm_alg,pre_multiunit_sep_alg,disjoint_parts_pre_perm_alg}\<close>)
  cancel_pre_perm_alg
  by standard (transfer, clarsimp)

(* not no_unit_perm_alg *)

instantiation seppair :: (\<open>{halving_pre_perm_alg,pre_multiunit_sep_alg,disjoint_parts_pre_perm_alg}\<close>)
  halving_pre_perm_alg
begin
lift_definition halfof_seppair :: \<open>'a seppair \<Rightarrow> 'a seppair\<close> is
  \<open>\<lambda>(x, y). (halfof x, halfof y)\<close>
  by (clarsimp simp add: halfof_disjoint_preservation_left halfof_disjoint_preservation_right)
instance
  apply standard
    apply (transfer, clarsimp simp add: disjoint_sym halfof_additive_split
      halfof_disjoint_preservation halfof_self_disjoint; fail)
   apply (transfer, clarsimp simp add: disjoint_sym halfof_disjoint_preservation
      halfof_self_disjoint; fail)
  apply (transfer, clarsimp simp add: halfof_disjoint_preservation halfof_sepadd_distrib)
  done
end

instance seppair :: (\<open>{all_disjoint_pre_perm_alg,pre_multiunit_sep_alg,disjoint_parts_pre_perm_alg}\<close>)
  all_disjoint_pre_perm_alg
  by standard (simp add: disjoint_seppair_def)


section \<open> Separated Multi-sets of Names \<close>

text \<open> All elements are disjoint and plus is multiset addition. \<close>

typedef 'a sep_mset = \<open>UNIV :: 'a multiset set\<close>
  morphisms SepMset Rep_set_mset
  by blast

setup_lifting type_definition_sep_mset

instantiation sep_mset :: (type) plus
begin
lift_definition plus_sep_mset :: \<open>'a sep_mset \<Rightarrow> 'a sep_mset \<Rightarrow> 'a sep_mset\<close> is \<open>(+)\<close> .
instance ..
end

instantiation sep_mset :: (type) disjoint
begin
lift_definition disjoint_sep_mset :: \<open>'a sep_mset \<Rightarrow> 'a sep_mset \<Rightarrow> bool\<close> is \<open>\<lambda>_ _. True\<close> .
instance ..
end

instance sep_mset :: (type) pre_perm_alg
  by standard (transfer, force)+

instance sep_mset :: (type) perm_alg
  by standard (transfer, force)+

instantiation sep_mset :: (type) multiunit_sep_alg
begin
lift_definition unitof_sep_mset :: \<open>'a sep_mset \<Rightarrow> 'a sep_mset\<close> is \<open>\<lambda>_. {#}\<close> .
instance by standard (transfer, force)+
end

instantiation sep_mset :: (type) zero
begin
lift_definition zero_sep_mset :: \<open>'a sep_mset\<close> is \<open>{#}\<close> .
instance ..
end

instance sep_mset :: (type) sep_alg
  by standard (transfer, force)+


subsection \<open> Misc Sepalg Instances \<close>

instance sep_mset :: (type) dupcl_perm_alg
  by standard (transfer, force)+

instance sep_mset :: (type) allcompatible_perm_alg
  by standard

(* not a strong_sep_perm_alg *)

instance sep_mset :: (type) disjoint_parts_pre_perm_alg
  by standard (transfer, force)+

(* not a trivial_selfdisjoint_pre_perm_alg *)

lemma nat_cross_split:
  fixes a b x y :: \<open>nat\<close>
  assumes \<open>a + b = x + y\<close>
  shows \<open>\<exists>ax ay bx by.
    ax + ay = a \<and> bx + by = b \<and> ax + bx = x \<and> ay + by = y\<close>
  using assms
  apply (induct x arbitrary: y a b)
   apply force
  apply (clarsimp simp add: suc_eq_plus_iff2)
  apply (elim disjE)
   apply clarsimp
   apply (drule_tac x=y in meta_spec, drule_tac x=b' and y=b in meta_spec2, force)
  apply clarsimp
  apply (drule_tac x=y in meta_spec, drule_tac x=a and y=c' in meta_spec2, force)
  done

(* TODO: the instance for crosssplit_perm_alg is tricky, as it looks to involve choice.
         Isabelle multisets are finite, meaning nothing too funky should be going on;
         moreover, the law holds for plain natural numbers. *)
(*
instance sep_mset :: (type) crosssplit_perm_alg
proof (standard; transfer; simp del: ex_simps)
  fix a b x y :: \<open>'a multiset\<close>
  assume \<open>a + b = x + y\<close>
  then show \<open>\<exists>ax ay bx by. ax + ay = a \<and> bx + by = b \<and> ax + bx = x \<and> ay + by = y\<close>
    sorry
qed
*)

instance sep_mset :: (type) cancel_pre_perm_alg
  by standard (transfer, force)+

(* not a no_unit_perm_alg *)

(* not a halving_perm_alg *)

instance sep_mset :: (type) all_disjoint_pre_perm_alg
  by standard (simp add: disjoint_sep_mset_def)


section \<open> Negative Heaps \<close>

text \<open>
  Here, we construct a variant of positive negative heaps, that only records the negative
  \<^emph>\<open>domain\<close> and not the value (which is not clear). It also uses a \<^emph>\<open>multiset\<close>, which allows
  us to record several failures of existence.
\<close>

section \<open> Better Separated Pairs \<close>

typedef(overloaded) ('a, 'b) pnheap =
  \<open>{(h,N)|(h::'a \<rightharpoonup> 'b) (N :: 'a multiset). dom h \<inter> set_mset N = {}}\<close>
  by fast
setup_lifting type_definition_pnheap

lift_definition pheap :: \<open>('a, 'b) pnheap \<Rightarrow> ('a \<rightharpoonup> 'b)\<close> is \<open>fst\<close> .
lift_definition naddrs :: \<open>('a, 'b) pnheap \<Rightarrow> 'a multiset\<close> is \<open>snd\<close> .


instantiation pnheap :: (type, disjoint) disjoint
begin
lift_definition disjoint_pnheap :: \<open>('a, 'b) pnheap \<Rightarrow> ('a, 'b) pnheap \<Rightarrow> bool\<close> is
  \<open>\<lambda>(ha,Na) (hb,Nb).
    ha ## hb \<and>
    dom ha \<inter> set_mset Nb = {} \<and>
    set_mset Na \<inter> dom hb = {} \<and>
    set_mset Na \<inter> set_mset Nb = {}\<close> .
instance by standard
end

instantiation pnheap :: (type, plus) plus
begin
lift_definition plus_pnheap :: \<open>('a, 'b) pnheap \<Rightarrow> ('a, 'b) pnheap \<Rightarrow> ('a, 'b) pnheap\<close> is
  \<open>\<lambda>(ha :: 'a \<rightharpoonup> 'b, Na::'a multiset) (hb,Nb).
    if dom ha \<inter> set_mset Nb = {} \<and> dom hb \<inter> set_mset Na = {}
    then (ha + hb, Na + Nb)
    else (Map.empty, {#})\<close>
  by (clarsimp simp add: inf_sup_distrib1 inf_sup_distrib2)
instance by standard
end

instance pnheap :: (type, pre_perm_alg) pre_perm_alg
  apply standard
      apply (transfer, clarsimp simp add: inf_sup_distrib1 inf.commute partial_add_assoc; fail)
     apply (transfer, clarsimp, metis partial_add_commute)
    apply (transfer, clarsimp simp add: inf.commute disjoint_sym_iff; fail)
   apply (transfer, clarsimp simp add: inf.commute inf_sup_distrib1,
      meson disjoint_add_rightL disjoint_fun_def; fail)
  apply (transfer, clarsimp simp add: inf.commute inf_sup_distrib1
      disjoint_add_right_commute disjoint_fun_def; fail)
  done


instance pnheap :: (type, positivity_law) positivity_law
  by standard
    (transfer, clarsimp simp add: inf.commute inf_sup_distrib1, meson positivity)

instantiation pnheap :: (type, pre_multiunit_sep_alg) pre_multiunit_sep_alg
begin
lift_definition unitof_pnheap :: \<open>('a, 'b) pnheap \<Rightarrow> ('a, 'b) pnheap\<close> is
  \<open>\<lambda>(h, N). (unitof h, {#})\<close>
  by (clarsimp simp add: disjoint_same_unit sepadd_unit_selfsep unitof_is_sepadd_unit)
instance
  by standard
    (transfer, clarsimp simp add: plus_fun_def)+
end

instance pnheap :: (type, multiunit_sep_alg) multiunit_sep_alg
  by standard

instantiation pnheap :: (type, zero) zero
begin
lift_definition zero_pnheap :: \<open>('a, 'b) pnheap\<close> is \<open>(Map.empty, {#})\<close>
  by blast
instance by standard
end

instance pnheap :: (type, pre_sep_alg) pre_sep_alg
  by standard (transfer, force)+


paragraph \<open> Special Laws \<close>

instance pnheap :: (type, disjoint_parts_pre_perm_alg) disjoint_parts_pre_perm_alg
  by standard
    (transfer, clarsimp simp add: inf.commute inf_sup_distrib1)

(* not a strong_sep_pre_perm_alg *)

instance pnheap :: (type, trivial_selfdisjoint_pre_perm_alg) trivial_selfdisjoint_pre_perm_alg
  by standard
    (transfer, force dest: selfdisjoint_same)

(* same crosssplit issue as above *)
(*
lemma multiset_crossplit:
  fixes a b c d :: \<open>'a multiset\<close>
  shows
  \<open>a + b = c + d \<Longrightarrow> \<exists>ac ad bc bd. ac + ad = a \<and> bc + bd = b \<and> ac + bc = c \<and> ad + bd = d\<close>
  apply (simp add: multiset_eq_iff)
  sledgehammer
  sorry
instance pnheap :: (type, crosssplit_pre_perm_alg) crosssplit_pre_perm_alg
  apply standard
  apply transfer
  apply (clarsimp simp add: inf.commute)
  apply (drule cross_split[rotated 2], blast, blast)
  apply (drule multiset_crossplit)
    (* pull out all existentials *)
  apply (clarsimp simp del: ex_simps simp add: ex_simps[symmetric]
      inf_sup_distrib1 inf_sup_distrib2)
  apply (simp only: imp_conjR[where Q=\<open>_ \<longrightarrow> _\<close> and R=\<open>_ \<longrightarrow> _\<close>] conj.assoc)
  apply (rename_tac max Nax may Nay mbx Nbx mby Nby)
  apply (rule_tac x=max in exI)
  apply (rule_tac x=Nax in exI)
  apply (rule_tac x=may in exI)
  apply (rule_tac x=Nay in exI)
  apply (clarsimp simp del: ex_simps)
  apply (rule_tac x=mbx in exI)
  apply (rule_tac x=Nbx in exI)
  apply (clarsimp simp del: ex_simps)
  apply (rule_tac x=mby in exI)
  apply (rule_tac x=Nby in exI)
  apply clarsimp
  done
*)

(* like option, only cancellative when the interior algebra has no units *)
instance pnheap :: (type, \<open>{cancel_pre_perm_alg,no_unit_pre_perm_alg}\<close>) cancel_pre_perm_alg
  by standard
    (transfer, clarsimp simp add: inf.commute)

(* not no_unit_perm_alg *)

lemma dom_halfof_eq[simp]:
  fixes m :: \<open>'a \<rightharpoonup> ('b::halving_pre_perm_alg)\<close>
  shows \<open>dom (halfof m) = dom m\<close>
  by (metis dom_plus_eq halfof_additive_split sup.idem)

(* not a halving_pre_perm_alg, due to the multiset *)

(* not an all_disjoint_pre_perm_alg *)


subsection \<open> Heap Operations \<close>

definition pnheap_mapsto_perm
  :: \<open>'pt \<Rightarrow> 'perm \<Rightarrow> ('s \<Rightarrow> 'v) \<Rightarrow> (('pt, 'v discr \<times> 'perm) pnheap \<times> 's \<Rightarrow> bool)\<close>
  (\<open>_ \<^bold>\<mapsto>\<^bsub>_\<^esub> _\<close> [55, 0, 55] 55)
  where
  \<open>pt \<^bold>\<mapsto>\<^bsub>\<pi>\<^esub> e \<equiv> \<lambda>(l,s). pheap l pt = Some (Discr (e s), \<pi>)\<close>

definition pnheap_failat
  :: \<open>'pt \<Rightarrow> (('pt, 'v discr \<times> 'perm) pnheap \<Rightarrow> bool)\<close> (\<open>\<crossmark>\<close>)
  where
  \<open>\<crossmark> pt \<equiv> \<lambda>l. count (naddrs l) pt = 1\<close>

subsubsection \<open> Read \<close>

lift_definition PointerRead_rel
  ::
  \<open>'x \<Rightarrow> 'pt \<Rightarrow>
    ('pt, 'v discr \<times> 'perm) pnheap \<times> ('x \<Rightarrow> 'v) \<Rightarrow>
    ('pt, 'v discr \<times> 'perm) pnheap \<times> ('x \<Rightarrow> 'v) \<Rightarrow>
    bool\<close>
  is \<open>\<lambda>x \<rho> (l, s) (l', s').
        (case fst l \<rho> of
          Some (v, _) \<Rightarrow> l' = l \<and> s' = s(x := the_discr v)
        | None \<Rightarrow> fst l' = fst l \<and> snd l' = add_mset \<rho> (snd l) \<and> s' = s)\<close>
  .

definition \<open>PointerRead x \<rho> \<equiv> Atomic (PointerRead_rel x \<rho>)\<close>

lemma rgsat_pointer_read_good:
  fixes x v p R \<pi> pt
  defines \<open>ra_ptr_read \<equiv> (=) \<times>\<^sub>R (\<lambda>s s'. s' = s(x := v))\<close>
  and \<open>precond \<equiv> (pt \<^bold>\<mapsto>\<^bsub>\<pi>\<^esub> (\<lambda>_. v)) \<sqinter> wssa R (\<S> (\<lambda>s. p (s(x := v))))\<close>
  and \<open>postcond \<equiv> (pt \<^bold>\<mapsto>\<^bsub>\<pi>\<^esub> (\<lambda>_. v)) \<sqinter> sswa R (\<S> p)\<close>
assumes
    \<open>rel_image snd ra_ptr_read \<le> G\<close>
    \<open>precond \<le> I\<close>
    \<open>postcond \<le> I\<close>
    \<open>T RGSepAtom\<close>
  shows
    \<open>R, G, I, F, T \<turnstile> { precond } PointerRead x pt { postcond }\<close>
  using assms
  unfolding PointerRead_def
  oops
(*
proof (intro rgsat_atom[where p=\<open>precond\<close> and q=\<open>postcond\<close>])

  show \<open>precond \<le> wssa (R \<times>\<^sub>R (=)) precond\<close>
    unfolding precond_def
    by (simp add: wlp_inf)

  show \<open>sswa (R \<times>\<^sub>R (=)) (postcond) \<le> postcond\<close>
    unfolding postcond_def
    by simp

  show \<open>sp ?ra' (precond) \<le> postcond\<close>
    using assms(1) precond_def postcond_def
    by (force simp add: sp_step_fail_lift_on_nofailure_pred_eq sepconj_conj_def
        points_to_def plus_option_iff)

  show \<open>\<forall>f\<le>F. sp ?ra' (precond \<^emph>\<and> f) \<le> postcond \<^emph>\<and> any_shared f\<close>
    unfolding any_shared_def ra_ptr_read_def precond_def postcond_def
    apply (clarsimp simp add: sp_step_fail_lift_on_nofailure_pred_eq subset_nofailure_pred_iff
        predTimes3_sepconj_conj_distrib[symmetric] case_option_disj_iff)
    apply (clarsimp simp add: sepconj_conj_def points_to_def plus_option_iff)
    apply (metis (mono_tags, lifting) Discr_inverse_iff comp_apply snd_conv sswa_trivial wssa_trivial)
    done

  show
    \<open>rel_image snd
      (rel_liftL (precond \<squnion> precond \<^emph>\<and> F) \<sqinter> ?ra')
    \<le> G \<times>\<^sub>R (=)\<close>
    using assms(4)
    apply (simp only: predTimes3_sepconj_conj_distrib[symmetric] predTimes3_sup_distrib[symmetric])
    apply (unfold ra_ptr_read_def precond_def postcond_def)
    apply (clarsimp simp add: sepconj_conj_def points_to_def plus_option_iff rel_image_def
        le_fun_def ex_disj_distrib all_conj_distrib split: option.splits)
    apply (elim disjE exE conjE)
     apply (simp; fail)
    apply (force simp add: wlp_def plus_option_iff ex_disj_distrib all_conj_distrib)
    done
qed simp+
*)

lemma stable_some_pnheap_mapsto_perm_pred:
  \<open>wssa R (\<Squnion>\<pi>. \<Squnion> range (pnheap_mapsto_perm pt \<pi>)) = (\<Squnion>\<pi>. \<Squnion> range (pnheap_mapsto_perm pt \<pi>))\<close>
  by (force simp add: pnheap_mapsto_perm_def fun_eq_iff wlp_def)

lemma stable_no_pnheap_mapsto_perm_pred:
  \<open>wssa R (-(\<Squnion>\<pi>. \<Squnion> range (pnheap_mapsto_perm pt \<pi>))) = -(\<Squnion>\<pi>. \<Squnion> range (pnheap_mapsto_perm pt \<pi>))\<close>
  by (force simp add: pnheap_mapsto_perm_def fun_eq_iff wlp_def)

lemma rgsat_pointer_read_bad:
  fixes x v p R \<pi> pt
  defines \<open>precond  \<equiv> wssa R (\<S> p) \<sqinter> -(\<Squnion>\<pi> e. pt \<^bold>\<mapsto>\<^bsub>\<pi>\<^esub> e)\<close>
  and     \<open>postcond \<equiv> wssa R (\<S> p) \<sqinter> \<L> (\<crossmark> pt)\<close>
assumes
    \<open>F \<le> -(\<Squnion>\<pi> e. pt \<^bold>\<mapsto>\<^bsub>\<pi>\<^esub> e)\<close>
    \<open>(=) \<le> G\<close>
    \<open>sswa R precond \<le> I\<close>
    \<open>sswa R postcond \<le> I\<close>
    \<open>T RGSepAtom\<close>
  shows
    \<open>R, G, I, F, T \<turnstile> { precond } PointerRead x pt { postcond }\<close>
  using assms
  unfolding PointerRead_def
proof (intro rgsat_atom[where p=\<open>precond\<close> and q=\<open>postcond\<close>])
  show \<open>precond \<le> wssa R precond\<close>
    unfolding precond_def
    by (clarsimp simp add: wlp_inf stable_no_pnheap_mapsto_perm_pred)
  show \<open>sswa R postcond \<le> postcond\<close>
    unfolding postcond_def
    by clarsimp
  show \<open>sp (PointerRead_rel x pt) precond \<le> postcond\<close>
    apply (clarsimp simp add: precond_def postcond_def sp_def PointerRead_rel.rep_eq le_fun_def
        split: prod.splits option.splits)
    sorry
  show \<open>\<forall>f\<le>F. sp (PointerRead_rel x pt) (precond \<^emph>\<and> f) \<le> postcond \<^emph>\<and> any_shared f\<close>
    apply (clarsimp simp add: precond_def postcond_def sp_def PointerRead_rel.rep_eq le_fun_def
        split: prod.splits option.splits)
    sorry
  show \<open>rel_image snd (rel_liftL (precond \<squnion> precond \<^emph>\<and> F) \<sqinter> PointerRead_rel x pt) \<le> G\<close>
    apply (clarsimp simp add: precond_def postcond_def sp_def PointerRead_rel.rep_eq
        split: prod.splits option.splits)
    sorry
qed simp+

subsection \<open> Write \<close>

definition PointerWrite
  :: \<open>'pt \<Rightarrow> ('s \<Rightarrow> 'v) \<Rightarrow> (('pt \<rightharpoonup> 'v discr \<times> 'perm) \<times> ('s \<times> fail_st)) comm\<close>
  where
    \<open>PointerWrite pt e \<equiv>
      Atomic (step_fail_lift (\<lambda>(l, s) (l', s', fl').
        case l pt of
          Some (_, perm) \<Rightarrow> l' = l(pt \<mapsto> (Discr (e s), perm)) \<and> s' = s \<and> fl' = Running
        | None \<Rightarrow> l' = l \<and> s' = s \<and> fl' = Failed
      ))\<close>

lemma top_write_frame_cond_iff_all_disjoint_perm:
  \<open>\<top> \<le> - \<L> (\<Squnion>x'\<in>Collect ((##) (Discr v, \<pi>)). pt \<^bold>\<mapsto>\<^sup>\<Up> x') \<longleftrightarrow> (\<forall>\<pi>'. \<not> \<pi> ## \<pi>')\<close>
  by (force simp add: points_to_upcl_def le_fun_def)

lemma nofailure_pred_any_shared_semidistrib:
  \<open>(any_shared p) \<le> any_shared (p)\<close>
  by (simp add: nofailure_pred_def any_shared_def le_fun_def)


subsection \<open> Alloc \<close>

subsection \<open> Free \<close>

end