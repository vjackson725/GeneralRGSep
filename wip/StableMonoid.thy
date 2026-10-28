theory StableMonoid
  imports "../SepLogic"
begin

text \<open>
  Stabilised permission algebras also form a permission algebra.
  From \<^emph>\<open>Thomas Dinsdale-Young Et. Al. Views: Compositional Reasoning for Concurrent Programs\<close>.
\<close>

typedef(overloaded) ('a::pre_multiunit_sep_alg) stable_res =
  \<open>{(A::'a \<Rightarrow> bool, R::'a \<Rightarrow> 'a \<Rightarrow> bool).
      \<comment> \<open> stable \<close>
      (\<forall>a a'. R\<^sup>*\<^sup>* a a' \<longrightarrow> A a \<longrightarrow> A a') \<and>
      \<comment> \<open> R preserves splits \<close>
      (\<forall>a b ab'. R\<^sup>*\<^sup>* (a + b) ab' \<longrightarrow> a ## b \<longrightarrow> (\<exists>a' b'. a' ## b' \<and> R\<^sup>*\<^sup>* a a' \<and> R\<^sup>*\<^sup>* b b' \<and> ab' = a' + b')) \<and>
      \<comment> \<open> R preserves unitof \<close>
      (\<forall>a ua'. R\<^sup>*\<^sup>* (unitof a) ua' \<longrightarrow> (\<exists>a'. R\<^sup>*\<^sup>* a a' \<and> unitof a' = ua'))
  }\<close>
  by (rule exI[of _ \<open>(\<bottom>, (=))\<close>]) simp

(* alternatively?
      \<comment> \<open> R preserves nondisjointness \<close>
      (\<forall>a a'. R\<^sup>*\<^sup>* a a' \<longrightarrow> All ((#/#) a) \<longrightarrow> All ((#/#) a'))
      \<comment> \<open> R preserves disjointness \<close>
      (\<forall>a a' f. R\<^sup>*\<^sup>* a a' \<longrightarrow> a ## f \<longrightarrow> a' ## f)
*)

setup_lifting type_definition_stable_res


instantiation stable_res :: (pre_multiunit_sep_alg) disjoint
begin
lift_definition disjoint_stable_res :: \<open>'a stable_res \<Rightarrow> 'a stable_res \<Rightarrow> bool\<close> is
  \<open>\<lambda>(A, Ra) (B, Rb). (\<exists>a b. A a \<and> B b \<and> a ## b) \<and> Ra = Rb\<close> .
instance ..
end

instantiation stable_res :: (pre_multiunit_sep_alg) plus
begin
lift_definition plus_stable_res :: \<open>'a stable_res \<Rightarrow> 'a stable_res \<Rightarrow> 'a stable_res\<close> is
  \<open>\<lambda>(A::'a \<Rightarrow> bool, R::'a \<Rightarrow> 'a \<Rightarrow> bool) (B, _).
    ( sp R\<^sup>*\<^sup>* (\<lambda>ab. \<exists>a b. a ## b \<and> ab = a + b \<and> A a \<and> B b), R )\<close>
  apply (clarsimp simp add: sp_def)
  apply (metis rtranclp_trans)
  done
instance ..
end

instance stable_res :: (pre_multiunit_sep_alg) pre_perm_alg
  apply standard
    (* plus assoc *)
    (** \<Rightarrow> *)
      apply transfer
      apply (clarsimp simp add: sp_def inf.assoc[symmetric] split: prod.splits)
      apply (rename_tac A R B C ax bx "by" ay cx cy)
      apply (intro ext iffI allI impI)
       apply clarsimp
       apply (rename_tac abc'' ab' c' a b)
       apply (subgoal_tac \<open>\<exists>ab'' c''. ab'' ## c'' \<and> abc'' = ab'' + c'' \<and> R\<^sup>*\<^sup>* ab' ab'' \<and> R\<^sup>*\<^sup>* c' c''\<close>)
        prefer 2
        apply metis
       apply (subgoal_tac \<open>\<exists>a' b'. a' ## b' \<and> ab' = a' + b' \<and> R\<^sup>*\<^sup>* a a' \<and> R\<^sup>*\<^sup>* b b'\<close>)
        prefer 2
        apply metis
       apply clarsimp
       apply (subgoal_tac \<open>\<exists>a'' b''. a'' ## b'' \<and> ab'' = a'' + b'' \<and> R\<^sup>*\<^sup>* a' a'' \<and> R\<^sup>*\<^sup>* b' b''\<close>)
        prefer 2
        apply metis
       apply (metis disjoint_add_leftR disjoint_add_swap_lr partial_add_assoc2 rtranclp.rtrancl_refl)
    (** \<Leftarrow> *)
      apply clarsimp
      apply (rename_tac abc'' a' bc' b c)
      apply (subgoal_tac \<open>\<exists>a'' bc''. a'' ## bc'' \<and> abc'' = a'' + bc'' \<and> R\<^sup>*\<^sup>* a' a'' \<and> R\<^sup>*\<^sup>* bc' bc''\<close>)
       prefer 2
       apply metis
      apply (subgoal_tac \<open>\<exists>b' c'. b' ## c' \<and> bc' = b' + c' \<and> R\<^sup>*\<^sup>* b b' \<and> R\<^sup>*\<^sup>* c c'\<close>)
       prefer 2
       apply metis
      apply clarsimp
      apply (subgoal_tac \<open>\<exists>b'' c''. b'' ## c'' \<and> bc'' = b'' + c'' \<and> R\<^sup>*\<^sup>* b' b'' \<and> R\<^sup>*\<^sup>* c' c''\<close>)
       prefer 2
       apply metis
      apply clarsimp
      apply (rule_tac exI, rule conjI, assumption)
      apply (metis disjoint_add_rightL disjoint_add_swap_rl partial_add_assoc3 rtranclp.rtrancl_refl)
    (* plus comm *)
     apply transfer
     apply (clarsimp simp add: sp_def)
     apply (rename_tac A B R ax bx)
     apply (intro ext iffI)
      apply (meson disjoint_sym partial_add_commute)
     apply (meson disjoint_sym partial_add_commute)
    (* disjoint sym *)
    apply transfer
    apply (clarsimp simp add: sp_def)
    apply (metis disjoint_sym)
    (* disjoint splitting *)
   apply transfer
   apply (clarsimp simp add: sp_def)
   apply (metis disjoint_add_rightL)
    (* disjoint commute-through *)
  apply transfer
  apply (clarsimp simp add: sp_def)
  apply (metis disjoint_add_rightR disjoint_add_right_commute rtranclp.rtrancl_refl)
  done

instance stable_res :: (\<open>{pre_multiunit_sep_alg,positivity_law}\<close>) positivity_law
  apply standard
  apply clarsimp
  apply transfer
  apply (clarsimp simp add: sp_def)
  apply (rename_tac A C B R az xy' cz bz x y)
  apply (subgoal_tac \<open>\<exists>x' y'. x' ## y' \<and> xy' = x' + y' \<and> R\<^sup>*\<^sup>* x x' \<and> R\<^sup>*\<^sup>* y y'\<close>)
   prefer 2
   apply metis
  apply clarsimp
  apply (intro ext iffI)
   apply (rename_tac a)
    \<comment> \<open> This is probably going to run into the same problem as hypersets \<close>
  oops


instantiation stable_res :: (pre_multiunit_sep_alg) unitof
begin
lift_definition unitof_stable_res :: \<open>'a stable_res \<Rightarrow> 'a stable_res\<close> is
  \<open>\<lambda>(A, Ra::'a \<Rightarrow> 'a \<Rightarrow> bool). (pred_image unitof A, Ra)\<close>
  apply clarsimp
  apply metis
  done
instance ..
end

instance stable_res :: (pre_multiunit_sep_alg) pre_multiunit_sep_alg
  apply standard
   apply transfer
   apply clarsimp
  oops


end