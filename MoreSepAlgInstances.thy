theory MoreSepAlgInstances
  imports SepAlgInstances
begin

class bounded_distrib_lattice = distrib_lattice + bounded_lattice

context boolean_algebra
begin
subclass bounded_distrib_lattice
  by standard
end


section \<open> Error monad \<close>

text \<open>
  Unfortunately, Error does not, in most cases, form a separation algebra.
  The global non-cancellative nature of the Error value breaks the disjoint-subpart law.

  However, it does form a good instance when there are only trivial subparts.
  (I.e. when every element is disjoint.)
\<close>

datatype 'a error =
  Val (the_val: 'a)
  | Error

instantiation error :: (ord) ord
begin

fun less_eq_error :: \<open>'a error \<Rightarrow> 'a error \<Rightarrow> bool\<close> where
  \<open>less_eq_error _ Error = True\<close>
| \<open>less_eq_error Error (Val b) = False\<close>
| \<open>less_eq_error (Val a) (Val b) = (a \<le> b)\<close>

lemma less_eq_error_def:
  \<open>a \<le> b =
    (case b of
      Error \<Rightarrow> True
    | Val b \<Rightarrow>
      (case a of
        Error \<Rightarrow> False
      | Val a \<Rightarrow> a \<le> b))\<close>
  by (cases a; cases b; force)

fun less_error :: \<open>'a error \<Rightarrow> 'a error \<Rightarrow> bool\<close> where
  \<open>less_error Error _ = False\<close>
| \<open>less_error (Val a) Error = True\<close>
| \<open>less_error (Val a) (Val b) = (a < b)\<close>

lemma less_error_def:
  \<open>a < b =
    (case a of
      Error \<Rightarrow> False
    | Val a \<Rightarrow>
      (case b of
        Error \<Rightarrow> True
      | Val b \<Rightarrow> a < b))\<close>
  by (cases a; cases b; force)

instance proof qed

end

instantiation error :: (preorder) preorder
begin

instance proof
  fix x y z :: \<open>'a :: preorder error\<close>
  show \<open>(x < y) = (x \<le> y \<and> \<not> y \<le> x)\<close>
    by (simp add: less_eq_error_def less_error_def error.case_eq_if less_le_not_le)
  show \<open>x \<le> x\<close>
    by (simp add: less_eq_error_def error.case_eq_if)
  show \<open>x \<le> y \<Longrightarrow> y \<le> z \<Longrightarrow> x \<le> z\<close>
    by (force dest: order_trans simp add: less_eq_error_def split: error.splits)
qed

end


instantiation error :: (order) order_top
begin

definition \<open>top_error \<equiv> Error\<close>

instance proof
  fix x y z :: \<open>'a :: order error\<close>
  show \<open>x \<le> y \<Longrightarrow> y \<le> x \<Longrightarrow> x = y\<close>
    by (simp add: less_eq_error_def split: error.splits)
  show \<open>x \<le> top\<close>
    by (simp add: top_error_def)
qed

end

instantiation error :: (order_bot) order_bot
begin

definition \<open>bot_error = Val bot\<close>

instance proof
  fix a :: \<open>'a :: order_bot error\<close>
  show \<open>\<bottom> \<le> a\<close>
    by (simp add: bot_error_def less_eq_error_def error.case_eq_if)
qed

end

instantiation error :: (all_disjoint_perm_alg) perm_alg
begin

definition disjoint_error :: \<open>'a error \<Rightarrow> 'a error \<Rightarrow> bool\<close> where
  \<open>disjoint_error a b \<equiv>
    a = Error \<or> b = Error \<or> (\<exists>x y. a = Val x \<and> b = Val y \<and> x ## y)\<close>

lemma disjoint_error_def2:
  \<open>a ## b \<longleftrightarrow> a = Error \<or> b = Error \<or> the_val a ## the_val b\<close>
  by (simp add: disjoint_error_def, metis error.exhaust)

lemma disjoint_error_simps[simp]:
  \<open>Error ## b\<close>
  \<open>a ## Error\<close>
  \<open>Val x ## Val y \<longleftrightarrow> x ## y\<close>
  by (simp add: disjoint_error_def)+


definition plus_error :: \<open>'a error \<Rightarrow> 'a error \<Rightarrow> 'a error\<close> where
  \<open>a + b \<equiv> case a of Val x \<Rightarrow> (case b of Val y \<Rightarrow> Val (x + y) | Error \<Rightarrow> Error) | Error \<Rightarrow> Error\<close>

lemma plus_error_def2:
  \<open>a + b = (if a = Error \<or> b = Error then Error else Val (the_val a + the_val b))\<close>
  by (simp add: error.case_eq_if plus_error_def)

lemma plus_error_simps[simp]:
  \<open>Error + b = Error\<close>
  \<open>a + Error = Error\<close>
  \<open>Val x + Val y = Val (x + y)\<close>
  by (force simp add: plus_error_def split: error.splits)+


instance
  apply standard
       apply (force simp add: disjoint_error_def plus_error_def partial_add_assoc
      split: error.splits)
      apply (force simp add: disjoint_error_def plus_error_def partial_add_commute
      split: error.splits)
     apply (force simp add: disjoint_error_def plus_error_def disjoint_sym_iff)
    apply (simp add: disjoint_error_def plus_error_def disjoint_add_rightL split: error.splits;
      metis error.exhaust)
   apply (force simp add: disjoint_add_right_commute disjoint_error_def)
  apply (force simp add: disjoint_error_def positivity)
  done

end

end