theory DGEx
  imports "../Soundness"
begin

section \<open> Rely-Guarantee Sep-State \<close>

text \<open>
  The simple RG separation algebra, originally (TODO: check) suggested in \<^emph>\<open>Deny-Guarantee Reasoning\<close> (TODO: cite properly).
  This model is non-cancellative, which is why, in that paper, they introduce \<^emph>\<open>deny\<close> conditions.
\<close>

datatype 's rg_state =
  RGSt
    (rely: \<open>'s \<Rightarrow> 's \<Rightarrow> bool\<close>)
    (guar: \<open>'s \<Rightarrow> 's \<Rightarrow> bool\<close>)

instantiation rg_state :: (type) pre_perm_alg
begin

definition
  \<open>plus_rg_state (a :: 'a rg_state) (b :: 'a rg_state) \<equiv>
    RGSt (rely a \<sqinter> rely b) (guar a \<squnion> guar b)\<close>

definition
  \<open>disjoint_rg_state (a :: 'a rg_state) (b :: 'a rg_state) \<equiv> guar a \<le> rely b \<and> guar b \<le> rely a\<close>
  \<comment> \<open> can be \<open>True\<close> \<close>

instance
  by standard
    (force simp add: disjoint_rg_state_def plus_rg_state_def)+

end

instance rg_state :: (type) perm_alg
  apply standard
  apply (cut_tac rg_state.nchotomy)
  apply (frule_tac x=a in spec)
  apply (drule_tac x=b in spec)
  apply (clarsimp simp add: disjoint_rg_state_def plus_rg_state_def)
  apply (meson inf_antisym sup_antisym)
  done

instantiation rg_state :: (type) pre_multiunit_sep_alg
begin

definition
  \<open>unitof_rg_state (a :: 'a rg_state) \<equiv> RGSt (\<top>::'a \<Rightarrow> 'a \<Rightarrow> _) \<bottom>\<close>

instance
  by standard
    (force simp add: unitof_rg_state_def disjoint_rg_state_def plus_rg_state_def)+

end

instance rg_state :: (type) multiunit_sep_alg
  by standard

instantiation rg_state :: (type) pre_sep_alg
begin

definition
  \<open>zero_rg_state \<equiv> RGSt (\<top>::'a \<Rightarrow> 'a \<Rightarrow> _) \<bottom>\<close>

instance
  by standard
    (force simp add: zero_rg_state_def disjoint_rg_state_def plus_rg_state_def)+

end

instance rg_state :: (type) sep_alg
  by standard

subsection \<open> Extended Instances \<close>

instance rg_state :: (type) dupcl_perm_alg
  apply standard
  sorry

\<comment> \<open> yes, as it has a zero \<close>
instance rg_state :: (type) allcompatible_perm_alg
  by standard

(* not a strong_sep_perm_alg *)

instance rg_state :: (type) disjoint_parts_perm_alg
  by standard
    (simp add: disjoint_rg_state_def plus_rg_state_def)

instance rg_state :: (type) trivial_selfdisjoint_perm_alg
  by standard
    (simp add: disjoint_rg_state_def plus_rg_state_def)

lemma rgst_eq_iff:
  \<open>RGSt ar ag = b \<longleftrightarrow> rely b = ar \<and> guar b = ag\<close>
  using rg_state.collapse by blast

(* not?? a crosssplit_perm_alg *)
instance rg_state :: (type) crosssplit_perm_alg
  apply standard
  apply (clarsimp simp add: disjoint_rg_state_def plus_rg_state_def)
  apply (rule_tac x=\<open>RGSt (rely a \<squnion> rely c) (guar a \<sqinter> guar c)\<close> in exI)
  apply (rule_tac x=\<open>RGSt (rely a \<squnion> rely d) (guar a \<sqinter> guar d)\<close> in exI)
  apply (intro conjI)
    apply force
  apply force
  apply (rule_tac x=\<open>RGSt (rely b \<squnion> rely c) (guar b \<sqinter> guar c)\<close> in exI)
  apply (rule_tac x=\<open>RGSt (rely b \<squnion> rely d) (guar b \<sqinter> guar d)\<close> in exI)
  apply (clarsimp simp add: rgst_eq_iff inf_sup_distrib1[symmetric] sup_inf_distrib1[symmetric]
      sup.order_iff[symmetric])
  apply (intro conjI)
               apply force
              apply force
             apply force
            apply force
           apply force
          apply force
  find_theorems \<open>_ = _ \<squnion> _\<close> \<open>_ \<le> _\<close>
  apply (metis sup_inf_absorb)
  apply (metis (no_types, lifting) boolean_algebra.disj_conj_distrib inf_sup_distrib1 rg_state.exhaust_sel
      sup_inf_absorb)
  sorry

(* not a cancel_perm_alg *)

(* not a halving_per_alg for the trivial duplicating instance, as
  it is not always the case that \<open>guar a \<le> rely a\<close>. *)

(* not a no_unit_perm_alg *)

(* not a all_disjoint_perm_alg *)

end