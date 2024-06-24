theory SepAlgInstancesExperimental
  imports "../SepAlgInstances"
begin


section \<open> Locked resources \<close>

(* This doesn't work. *)

(* TODO: this might be better as a datatype. *)
type_synonym 'a locked = \<open>munit + 'a\<close>

abbreviation(input) \<open>Locked \<equiv> Inl \<one> :: 'a locked\<close>
abbreviation(input) \<open>Unlocked x \<equiv> Inr x :: 'a locked\<close>

lemma disjoint_locked_simps[simp]:
  \<open>\<And>b. Locked ## b \<longleftrightarrow> False\<close>
  \<open>\<And>a. a ## Locked \<longleftrightarrow> False\<close>
  \<open>\<And>a b. Unlocked a ## Unlocked b \<longleftrightarrow> a ## b\<close>
    apply (case_tac b; simp)
   apply (case_tac a; simp)
  apply simp
  done

type_synonym 'a resources = \<open>nat \<rightharpoonup> 'a locked\<close>


section \<open> Max algebra \<close>

typedef(overloaded) ('a::order) max_res =
  \<open>{x::'a\<times>'a. fst x \<le> snd x}\<close>
  by auto

setup_lifting type_definition_max_res

instantiation max_res :: (canonically_ordered_monoid_add) perm_alg
begin

lift_definition disjoint_max_res :: \<open>'a max_res \<Rightarrow> 'a max_res \<Rightarrow> bool\<close> is
  \<open>\<lambda>x y. snd x = snd y\<close> .

lift_definition plus_max_res :: \<open>'a max_res \<Rightarrow> 'a max_res \<Rightarrow> 'a max_res\<close> is
  \<open>\<lambda>(x,m) (y,_). (min (x + y) m, m)\<close>
  by (clarsimp simp add: min_def split: prod.splits)

instance
  apply standard
  subgoal
    apply transfer
    apply (clarsimp simp add: min_def split: prod.splits)
    apply (intro conjI impI allI)
                        apply (metis add.commute add.left_commute)
                        apply (metis add.commute add.left_commute le_iff_add)
                       apply (metis add.commute add.left_commute)
                      apply (metis add.commute add.left_commute)
                     apply (metis add.commute add.left_commute)
                    apply (metis add.commute add.left_commute le_iff_add)
                   apply (metis add.commute add.left_commute)
                  apply (metis add.commute add.left_commute)
                 apply (metis add.commute add.left_commute)
                apply (metis order_eq_iff le_iff_add)
               apply (metis add.commute add.left_commute)
              apply (metis add.commute add.left_commute le_iff_add)
             apply (metis add.commute add.left_commute le_iff_add)
            apply (metis add.commute add.left_commute le_iff_add)
           apply (metis add.commute add.left_commute le_iff_add)
          apply (metis add.commute add.left_commute le_iff_add)
         apply (metis add.commute add.left_commute le_iff_add)
        apply (metis add.commute add.left_commute le_iff_add)
       apply (metis add.commute add.left_commute le_iff_add)
      apply (metis add.commute add.left_commute le_iff_add)
     apply (metis add.commute add.left_commute le_iff_add)
    apply (metis add.commute le_iff_add order_eq_iff)
    done
      apply (transfer, clarsimp simp add: add.commute split: prod.splits; fail)
     apply (transfer, simp; fail)
    apply (transfer, simp split: prod.splits; fail)
   apply (transfer, clarsimp split: prod.splits; fail)
  apply (transfer, clarsimp split: prod.splits, metis le_iff_add min_absorb2 min_def)
  done

end



end