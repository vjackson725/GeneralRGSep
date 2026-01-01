theory RGAlg
  imports "../RGLogic"
begin


section \<open> Rely-Guarantee Separation Algebra \<close>

text \<open> Criss-cross pairs.
  This separation algebra idea was first proposed in the Deny-Guarantee paper (TODO: proper cite).
  Of course, to actually set up rely-guarantee, you also need a notion of stabilisation,
  which we will set up later.

  Note we do \<^emph>\<open>not\<close> take the reflexive transitive closure of the guarantee,
  as our guarantee relation represents the possible \<^emph>\<open>atomic\<close> actions.
\<close>
datatype 'l ccpair = CCPair (ccfst: 'l) (ccsnd: 'l)

lemma ex_ccpair_of_fstsnd_pred_iff:
  \<open>(\<exists>a::'a ccpair. P (ccfst a) (ccsnd a)) \<longleftrightarrow> (\<exists>ra ga. P ra ga)\<close>
  by (metis ccpair.sel(1,2))


subsection \<open> sepalg instance \<close>

instantiation ccpair :: (order) disjoint
begin
definition \<open>disjoint_ccpair (a::'a ccpair) b \<equiv> ccsnd a \<le> ccfst b \<and> ccsnd b \<le> ccfst a\<close>
instance by standard
end

instantiation ccpair :: (lattice) plus
begin
definition \<open>plus_ccpair (a::'a ccpair) b \<equiv> CCPair (ccfst a \<sqinter> ccfst b) (ccsnd a \<squnion> ccsnd b)\<close>
instance by standard
end

lemma ccfst_ccsnd_plus_eq[simp]:
  \<open>ccfst (a + b) = ccfst a \<sqinter> ccfst b\<close>
  \<open>ccsnd (a + b) = ccsnd a \<squnion> ccsnd b\<close>
  by (simp add: plus_ccpair_def)+


instance ccpair :: (lattice) pre_perm_alg
  apply standard
      apply (simp add: disjoint_ccpair_def plus_ccpair_def inf.assoc sup.assoc; fail)
     apply (simp add: disjoint_ccpair_def plus_ccpair_def inf.commute sup.commute)+
  done

instance ccpair :: (lattice) positivity_law
  apply standard
  apply (clarsimp simp add: disjoint_ccpair_def plus_ccpair_def)
  apply (metis ccpair.sel inf_antisym sup_antisym)
  done

instantiation ccpair :: (bounded_lattice) pre_multiunit_sep_alg
begin
definition \<open>unitof_ccpair (_::'a ccpair) \<equiv> CCPair \<top> \<bottom>::'a ccpair\<close>
instance
  by standard
    (simp add: unitof_ccpair_def disjoint_ccpair_def plus_ccpair_def)+
end

lemma ccfst_ccsnd_unitof_eq[simp]:
  \<open>ccfst (unitof a) = \<top>\<close>
  \<open>ccsnd (unitof a) = \<bottom>\<close>
  by (simp add: unitof_ccpair_def)+


instantiation ccpair :: (bounded_lattice) zero
begin
definition \<open>zero_ccpair \<equiv> CCPair \<top> \<bottom>::'a ccpair\<close>
instance by standard
end

lemma ccfst_ccsnd_zero_eq[simp]:
  \<open>ccfst 0 = \<top>\<close>
  \<open>ccsnd 0 = \<bottom>\<close>
  by (simp add: zero_ccpair_def)+


instance ccpair :: (bounded_lattice) pre_sep_alg
  by standard
    (simp add: zero_ccpair_def disjoint_ccpair_def plus_ccpair_def)+


subsubsection \<open> Extended resalg laws \<close>

instance ccpair :: (lattice) dupcl_perm_alg
  by standard
    (simp add: plus_ccpair_def disjoint_ccpair_def)

(* not strong_sep_pre_perm_alg *)

instance ccpair :: (lattice) disjoint_parts_pre_perm_alg
  by standard (simp add: disjoint_ccpair_def plus_ccpair_def)

instance ccpair :: (lattice) trivial_selfdisjoint_pre_perm_alg
  by standard (simp add: disjoint_ccpair_def plus_ccpair_def)

instance ccpair :: (distrib_lattice) crosssplit_pre_perm_alg
  apply standard
  apply (case_tac a, case_tac b, case_tac c, case_tac d)
  apply (clarsimp simp add: disjoint_ccpair_def plus_ccpair_def)
  apply (subst ex_ccpair_of_fstsnd_pred_iff)+
  apply clarsimp
  apply (drule inf_crosssplit)
  apply (drule sup_crosssplit)
  apply clarsimp
  apply blast (* slow-ish *)
  done

(* not a cancel_pre_perm_alg *)
(* not a halving_pre_perm_alg *)

instance ccpair :: (bounded_lattice) allcompatible_perm_alg
  by standard
    (metis zero_least trans_ge_le_is_compatible)

(* not an all_disjoint_pre_perm_alg *)
(* not a no_unit_pre_perm_alg *)


subsubsection \<open> Lattice Instance \<close>

instantiation ccpair :: (ord) ord
begin
definition less_eq_ccpair :: \<open>'a ccpair \<Rightarrow> 'a ccpair \<Rightarrow> bool\<close> where
  \<open>less_eq_ccpair a b \<equiv> ccfst a \<le> ccfst b \<and> ccsnd a \<ge> ccsnd b\<close>

definition less_ccpair :: \<open>'a ccpair \<Rightarrow> 'a ccpair \<Rightarrow> bool\<close> where
  \<open>less_ccpair x y \<equiv> x \<le> y \<and> \<not> y \<le> x\<close>
instance by standard
end

lemma less_ccpair_iff:
  fixes a b :: \<open>('a::order) ccpair\<close>
  shows
    \<open>a < b \<longleftrightarrow>
      ccfst a < ccfst b \<and> ccsnd a \<ge> ccsnd b \<or> ccfst a \<le> ccfst b \<and> ccsnd a > ccsnd b\<close>
  using less_ccpair_def less_eq_ccpair_def by auto

instance ccpair :: (preorder) preorder
  by standard
    (force simp add: less_ccpair_def less_eq_ccpair_def dest: order.trans)+

instance ccpair :: (order) order
  by standard
    (force simp add: less_ccpair_def less_eq_ccpair_def ccpair.expand order.eq_iff)


instantiation ccpair :: (\<open>{inf, sup}\<close>) inf
begin
definition inf_ccpair :: \<open>'a ccpair \<Rightarrow> 'a ccpair \<Rightarrow> 'a ccpair\<close> where
  \<open>inf_ccpair a b \<equiv> CCPair (ccfst a \<sqinter> ccfst b) (ccsnd a \<squnion> ccsnd b)\<close>
instance by standard
end

lemma ccfst_ccsnd_inf_eq[simp]:
  \<open>ccfst (a \<sqinter> b) = ccfst a \<sqinter> ccfst b\<close>
  \<open>ccsnd (a \<sqinter> b) = ccsnd a \<squnion> ccsnd b\<close>
  by (simp add: inf_ccpair_def)+

instantiation ccpair :: (\<open>{inf, sup}\<close>) sup
begin
definition sup_ccpair :: \<open>'a ccpair \<Rightarrow> 'a ccpair \<Rightarrow> 'a ccpair\<close> where
  \<open>sup_ccpair a b \<equiv> CCPair (ccfst a \<squnion> ccfst b) (ccsnd a \<sqinter> ccsnd b)\<close>
instance by standard
end

lemma ccfst_ccsnd_sup_eq[simp]:
  \<open>ccfst (a \<squnion> b) = ccfst a \<squnion> ccfst b\<close>
  \<open>ccsnd (a \<squnion> b) = ccsnd a \<sqinter> ccsnd b\<close>
  by (simp add: sup_ccpair_def)+


instance ccpair :: (lattice) semilattice_inf
  by standard
    (simp add: inf_ccpair_def less_eq_ccpair_def)+

instance ccpair :: (lattice) semilattice_sup
  by standard
    (simp add: sup_ccpair_def less_eq_ccpair_def)+

instance ccpair :: (distrib_lattice) distrib_lattice
  by standard
    (simp add: sup_ccpair_def inf_ccpair_def, meson inf_sup_distrib1 sup_inf_distrib1)

paragraph \<open> Bounded Lattice \<close>

instantiation ccpair :: (\<open>{top,bot}\<close>) top
begin
definition top_ccpair :: \<open>'a ccpair\<close> where
  \<open>top_ccpair \<equiv> CCPair \<top> \<bottom>\<close>
instance by standard
end

lemma ccfst_ccsnd_top_eq[simp]:
  \<open>ccfst \<top> = \<top>\<close>
  \<open>ccsnd \<top> = \<bottom>\<close>
  by (simp add: top_ccpair_def)+


instantiation ccpair :: (\<open>{top,bot}\<close>) bot
begin
definition bot_ccpair :: \<open>'a ccpair\<close> where
  \<open>bot_ccpair \<equiv> CCPair \<bottom> \<top>\<close>
instance by standard
end

lemma ccfst_ccsnd_bot_eq[simp]:
  \<open>ccfst \<bottom> = \<bottom>\<close>
  \<open>ccsnd \<bottom> = \<top>\<close>
  by (simp add: bot_ccpair_def)+


instance ccpair :: (\<open>{order_top, order_bot}\<close>) order_top
  by standard
    (simp add: less_eq_ccpair_def top_ccpair_def)

instance ccpair :: (\<open>{order_top, order_bot}\<close>) order_bot
  by standard
    (simp add: less_eq_ccpair_def bot_ccpair_def)


paragraph \<open> Boolean Algebra \<close>

instantiation ccpair :: (uminus) uminus
begin
definition uminus_ccpair :: \<open>'a ccpair \<Rightarrow> 'a ccpair\<close> where
  \<open>uminus_ccpair a \<equiv> CCPair (- ccfst a) (- ccsnd a)\<close>
instance by standard
end

lemma ccfst_ccsnd_uminus_eq[simp]:
  \<open>ccfst (-a) = - ccfst a\<close>
  by (simp add: uminus_ccpair_def)+

instantiation ccpair :: (\<open>{uminus,minus}\<close>) minus
begin
definition minus_ccpair :: \<open>'a ccpair \<Rightarrow> 'a ccpair \<Rightarrow> 'a ccpair\<close> where
  \<open>minus_ccpair a b \<equiv> CCPair (ccfst a - ccfst b) (-(ccsnd b - ccsnd a))\<close>
instance by standard
end

instance ccpair :: (boolean_algebra) boolean_algebra
  by standard
    (simp add: sup_ccpair_def inf_ccpair_def minus_ccpair_def uminus_ccpair_def
      bot_ccpair_def top_ccpair_def diff_eq sup.commute)+


subsection \<open> Rely-Guarantee \<close>

\<comment> \<open>
  We use stable \<^emph>\<open>assertions\<close> here, rather than states in a quotient type,
  because it is \<^emph>\<open>not\<close> necessarily the case that
    \<open>ra\<^sup>*\<^sup>* sa = ra\<^sup>*\<^sup>* sb \<Longrightarrow> rb\<^sup>*\<^sup>* sa = rb\<^sup>*\<^sup>* sb \<Longrightarrow> (ra \<sqinter> rb)\<^sup>*\<^sup>* sa = (ra \<sqinter> rb)\<^sup>*\<^sup>* sb\<close>.
\<close>

typedef 'a rgsep =
  \<open>{(RG::('a \<Rightarrow> 'a \<Rightarrow> bool) ccpair, p::('a \<Rightarrow> bool)). sp (ccfst RG)\<^sup>*\<^sup>* p \<le> p}\<close>
  morphisms Rep_rgsep RGSep
  by blast

setup_lifting type_definition_rgsep

subsubsection \<open> projection functions \<close>

lift_definition rgrels :: \<open>'a rgsep \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) ccpair\<close> is \<open>fst\<close> .
lift_definition rgstates :: \<open>'a rgsep \<Rightarrow> ('a \<Rightarrow> bool)\<close> is \<open>snd\<close> .

lemma rgrels_eq[simp]:
  \<open>sp (ccfst RG)\<^sup>*\<^sup>* S \<le> S \<Longrightarrow> rgrels (RGSep (RG, S)) = RG\<close>
  by (simp add: RGSep_inverse rgrels.rep_eq)

lemma rgstates_eq[simp]:
  \<open>sp (ccfst RG)\<^sup>*\<^sup>* S \<le> S \<Longrightarrow> rgstates (RGSep (RG, S)) = S\<close>
  by (simp add: RGSep_inverse rgstates.rep_eq)


subsubsection \<open> sepalg instance \<close>

instantiation rgsep :: (type) disjoint
begin
lift_definition disjoint_rgsep :: \<open>'a rgsep \<Rightarrow> 'a rgsep \<Rightarrow> bool\<close> is
  \<open>\<lambda>(RGa, pa) (RGb, pb). RGa ## RGb\<close> .
instance by standard
end

lemmas disjoint_rgsep_abs_eq[simp] =
  disjoint_rgsep.abs_eq[simplified eq_onp_same_args mem_Collect_eq split_beta]

instantiation rgsep :: (type) plus
begin
lift_definition plus_rgsep :: \<open>'a rgsep \<Rightarrow> 'a rgsep \<Rightarrow> 'a rgsep\<close> is
  \<open>\<lambda>(RGa, Sa) (RGb, Sb). (RGa + RGb, Sa \<sqinter> Sb)\<close>
  by (simp split: prod.splits, meson order.trans inf.cobounded2 inf_le1 rtranclp_mono sp_mono)
instance by standard
end

lemmas plus_rgsep_abs_eq[simp] =
  plus_rgsep.abs_eq[simplified eq_onp_same_args mem_Collect_eq split_beta]

lemma rgsep_plus_eq_RGSep_iff:
  \<open>sp (ccfst RG)\<^sup>*\<^sup>* S \<le> S \<Longrightarrow>
    a + b = RGSep (RG, S) \<longleftrightarrow>
    (\<exists>RGa Sa. sp (ccfst RGa)\<^sup>*\<^sup>* Sa \<le> Sa \<and> a = RGSep (RGa, Sa) \<and>
      (\<exists>RGb Sb. sp (ccfst RGb)\<^sup>*\<^sup>* Sb \<le> Sb \<and> b = RGSep (RGb, Sb) \<and>
        RG = RGa + RGb \<and> S = Sa \<sqinter> Sb))\<close>
  apply (clarsimp simp add: Rep_rgsep_inject[symmetric] plus_rgsep.rep_eq RGSep_inverse split: prod.splits)
  apply (metis (no_types, lifting) Rep_rgsep Rep_rgsep_inverse mem_Collect_eq old.prod.case rgrels_eq
      rgstates_eq)
  done

instance rgsep :: (type) pre_perm_alg
  apply standard
      apply (transfer, clarsimp, metis partial_add_assoc inf.assoc)
     apply (transfer, clarsimp, metis partial_add_commute inf.commute)
    apply (transfer, clarsimp, metis disjoint_sym)
   apply (transfer, clarsimp; fail)
  apply (transfer, clarsimp, metis disjoint_sym)
  done

instance rgsep :: (type) positivity_law
  by standard
    (transfer, clarsimp simp add: positivity inf_antisym)

instantiation rgsep :: (type) pre_multiunit_sep_alg
begin
lift_definition unitof_rgsep :: \<open>'a rgsep \<Rightarrow> 'a rgsep\<close> is
  \<open>\<lambda>(RGa, Sa). (unitof RGa, \<top>)\<close>
  by clarsimp
instance
  by standard
    (transfer, clarsimp)+
end

instantiation rgsep :: (type) zero
begin
lift_definition zero_rgsep :: \<open>'a rgsep\<close> is \<open>(0, \<top>)\<close>
  by clarsimp
instance by standard
end

instance rgsep :: (type) pre_sep_alg
  by standard
    (transfer, clarsimp)+


subsubsection \<open> Extended sepalg laws \<close>

instance rgsep :: (type) dupcl_perm_alg
  by standard
    (transfer, clarsimp, metis selfdisjoint_same)

(* not strong_sep_pre_perm_alg *)

instance rgsep :: (type) disjoint_parts_pre_perm_alg
  by standard
    (transfer, clarsimp)

instance rgsep :: (type) trivial_selfdisjoint_pre_perm_alg
  apply standard
  apply (transfer, clarsimp)
  apply (metis all_selfdisjoint_dup sepadd_dup_def)
  done

text \<open>
  Not obviously a crosssplit_pre_perm_alg, as the cross-split property would require stability
  under sub-rely conditions and sub-predicates, which isn't true.
\<close>
lemma
  \<open>sp (ra \<sqinter> rb)\<^sup>*\<^sup>* (pa \<sqinter> pb) \<le> pa \<Longrightarrow> sp (ra \<sqinter> rb)\<^sup>*\<^sup>* pa \<le> pa\<close>
  nitpick[card 'a=2]
  oops

(* not a cancel_pre_perm_alg *)
(* not a halving_pre_perm_alg *)

instance rgsep :: (type) allcompatible_perm_alg
  by standard
    (simp add: same_unit_compatible)

(* not an all_disjoint_pre_perm_alg *)
(* not a no_unit_pre_perm_alg *)


subsubsection \<open> Lattice Instances \<close>

paragraph \<open> Order \<close>

instantiation rgsep :: (type) ord
begin
lift_definition less_eq_rgsep :: \<open>'a rgsep \<Rightarrow> 'a rgsep \<Rightarrow> bool\<close> is
  \<open>\<lambda>(RGa, Sa) (RGb, Sb). RGa \<le> RGb \<and> Sa \<le> Sb\<close> .
definition less_rgsep :: \<open>'a rgsep \<Rightarrow> 'a rgsep \<Rightarrow> bool\<close> where
  \<open>less_rgsep a b \<equiv> a \<le> b \<and> \<not> b \<le> a\<close>
instance by standard
end

instance rgsep :: (type) preorder
  by standard
    (force simp add: less_rgsep_def less_eq_rgsep_def dest: order.trans)+

instance rgsep :: (type) order
  by standard
    (transfer, clarsimp)


paragraph \<open> Lattice \<close>

instantiation rgsep :: (type) inf
begin
lift_definition inf_rgsep :: \<open>'a rgsep \<Rightarrow> 'a rgsep \<Rightarrow> 'a rgsep\<close> is
  \<open>\<lambda>(RGa, Sa) (RGb, Sb). (RGa \<sqinter> RGb, Sa \<sqinter> Sb)\<close>
  apply transfer
  apply (clarsimp simp add: le_fun_def sp_def imp_ex_conjL)
  apply (metis (no_types, lifting) inf2E mono_rtranclp)
  done
instance by standard
end

instantiation rgsep :: (type) sup
begin
lift_definition sup_rgsep :: \<open>'a rgsep \<Rightarrow> 'a rgsep \<Rightarrow> 'a rgsep\<close> is
  \<open>\<lambda>(RGa, Sa) (RGb, Sb). (RGa \<squnion> RGb, sp (ccfst RGa \<squnion> ccfst RGb)\<^sup>*\<^sup>* (Sa \<squnion> Sb))\<close>
  by transfer
    (clarsimp simp add: le_fun_def sp_def, meson rtranclp_trans)
instance by standard
end

\<comment> \<open> sup has a trickier definition, thus a trickier instance. \<close>
instance rgsep :: (type) semilattice_sup
  apply standard
    apply (transfer, clarsimp, metis rtranclp.rtrancl_refl sp_apply sup1CI)
   apply (transfer, clarsimp, metis rtranclp.rtrancl_refl sp_apply sup1CI)
  apply (transfer, clarsimp)
  apply (metis (mono_tags, lifting) le_supI less_eq_ccpair_def rev_predicate1D rtranclp_mono sp_mono)
  done

(* not a distrib_lattice *)


paragraph \<open> Bounded Lattice \<close>

instantiation rgsep :: (type) top
begin
lift_definition top_rgsep :: \<open>'a rgsep\<close> is \<open>(\<top>, \<top>)\<close>
  by clarsimp
instance by standard
end

instantiation rgsep :: (type) bot
begin
lift_definition bot_rgsep :: \<open>'a rgsep\<close> is \<open>(\<bottom>, \<bottom>)\<close>
  by clarsimp
instance by standard
end

instance rgsep :: (type) order_top
  by standard
    (transfer, clarsimp)

instance rgsep :: (type) order_bot
  by standard
    (transfer, clarsimp)

\<comment> \<open> Due to the stabilisation, there is no well defined inverse or psuedo-inverse. \<close>

subsection \<open> Properties \<close>

lemma rgsep_plus_decreasing:
  \<open>a ## b \<Longrightarrow> (a :: 'a rgsep) + b \<le> a\<close>
  apply transfer
  apply clarsimp
  apply (metis inf_ccpair_def inf_le1 plus_ccpair_def)
  done


section \<open> General Separation Logic \<close>

definition
  \<open>cancellative'' Ia Ib F \<equiv>
    \<forall>sa sb f.
      Ia sa \<longrightarrow> Ib sb \<longrightarrow>
      F f \<longrightarrow>
      sa ## f \<longrightarrow> sb ## f \<longrightarrow>
      sa + f = sb + f \<longrightarrow> sa = sb\<close>

inductive seplogic ::
  \<open>('l::pre_perm_alg) comm \<Rightarrow>
    ('l \<Rightarrow> bool) \<Rightarrow>
    ('l \<Rightarrow> bool) \<Rightarrow>
    ('l \<Rightarrow> bool) \<Rightarrow>
    ('l \<Rightarrow> bool) \<Rightarrow>
    (rgsep_rule \<Rightarrow> bool) \<Rightarrow>
    bool\<close>
  where
  seplogic_skip:
  \<open>p \<le> q \<Longrightarrow> p \<le> I \<Longrightarrow> T CCPairSkip \<Longrightarrow>
    seplogic Skip p q I F T\<close>
| seplogic_iter:
  \<open>seplogic c i i I F T \<Longrightarrow> p \<le> i \<Longrightarrow> i \<le> q \<Longrightarrow> T CCPairIter \<Longrightarrow>
    seplogic (Iter c) p q I F T\<close>
| seplogic_seq:
  \<open>seplogic ca p pp Ia F T \<Longrightarrow>
    seplogic cb pp q Ib F T \<Longrightarrow>
    Ia \<le> I \<Longrightarrow> Ib \<le> I \<Longrightarrow>
    T CCPairSeq \<Longrightarrow>
    seplogic (ca ;; cb) p q I F T\<close>
| seplogic_indet:
  \<open>seplogic ca p qa Ia F T \<Longrightarrow>
    seplogic cb p qb Ib F T \<Longrightarrow>
    qa \<le> q \<Longrightarrow> qb \<le> q \<Longrightarrow>
    Ia \<le> I \<Longrightarrow> Ib \<le> I \<Longrightarrow>
    T CCPairIndet \<Longrightarrow>
    seplogic (ca \<^bold>\<sqinter> cb) p q I F T\<close>
| seplogic_endet:
  \<open>seplogic ca p qa Ia F T \<Longrightarrow>
    seplogic cb p qb Ib F T \<Longrightarrow>
    qa \<le> q \<Longrightarrow> qb \<le> q \<Longrightarrow>
    T CCPairEndet \<Longrightarrow>
    seplogic (ca \<^bold>\<box> cb) p q I F T\<close>
| seplogic_par:
  \<open>seplogic ca pa qa Ia (Ib \<squnion> Ib \<^emph> F) T \<Longrightarrow>
    seplogic cb pb qb Ib (Ia \<squnion> Ia \<^emph> F) T \<Longrightarrow>
    p \<le> pa \<^emph> pb \<Longrightarrow>
    qa \<^emph> qb \<le> q \<Longrightarrow>
    Ia \<^emph> Ib \<le> I \<Longrightarrow>
    T CCPairPar \<Longrightarrow>
    seplogic (ca \<parallel> cb) p q I F T\<close>
| seplogic_atom:
  \<open>\<comment> \<open> step \<close>
    sp ar p \<le> q \<Longrightarrow>
    \<forall>f\<le>F. sp ar (p \<^emph> f) \<le> q \<^emph> f \<Longrightarrow> \<comment> \<open> TODO: any-shared condition \<close>
    \<comment> \<open> misc \<close>
    p \<le> I \<Longrightarrow>
    q \<le> I \<Longrightarrow>
    T CCPairAtom \<Longrightarrow>
    seplogic \<langle>ar\<rangle> p q I F T\<close>
| seplogic_frame:
  \<open>seplogic c p q I (F \<^emph> F' \<squnion> F') T \<Longrightarrow>
    T CCPairFrame \<Longrightarrow>
    seplogic c (p \<^emph> F') (q \<^emph> F') (I \<^emph> F') F T\<close>
| seplogic_weaken:
  \<open>seplogic c p' q' I' F' T \<Longrightarrow>
    p \<le> p' \<Longrightarrow>
    q' \<le> q \<Longrightarrow>
    I' \<le> I \<Longrightarrow>
    F \<le> F' \<Longrightarrow>
    T CCPairWeaken \<Longrightarrow>
    seplogic c p q I F T\<close>
| seplogic_Disj:
  \<open>p' \<le> \<Squnion>P \<Longrightarrow>
    \<forall>p\<in>P. seplogic c p q I F T \<Longrightarrow>
    T CCPairDisj \<Longrightarrow>
    seplogic c p' q I F T\<close>
| seplogic_Conj:
  \<open>\<Sqinter>\<I> \<le> I' \<Longrightarrow>
    \<I> \<noteq> {} \<Longrightarrow>
    Q \<noteq> {} \<Longrightarrow>
    \<forall>I\<in>\<I>. \<forall>q\<in>Q. seplogic c p q I F T \<Longrightarrow>
    cancellative'' (\<Squnion>\<I>) (\<Squnion>\<I>) F \<Longrightarrow>
    T CCPairConj \<Longrightarrow>
    seplogic c p q' I' F T\<close>


end