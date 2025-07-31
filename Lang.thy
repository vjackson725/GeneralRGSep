theory Lang
  imports SepAlgInstances "HOL-Library.Multiset"
begin

section \<open> Language Definition \<close>

subsection \<open> Termination Result \<close>

datatype tres = Term | Error


subsubsection \<open> TRes is an Order \<close>

instantiation tres :: ord
begin
definition \<open>less_eq_tres a b \<equiv> a = b \<or> a = Term \<and> b = Error\<close>
definition \<open>less_tres a b \<equiv> a = Term \<and> b = Error\<close>
instance by standard
end

instance tres :: preorder
  by standard (force simp add: less_eq_tres_def less_tres_def)+

instance tres :: order
  by standard (force simp add: less_eq_tres_def)+

lemma less_eq_tres_eq[simp]:
  \<open>Term \<le> a\<close>
  \<open>a \<le> Error\<close>
  \<open>Error \<le> a \<longleftrightarrow> a = Error\<close>
  \<open>a \<le> Term \<longleftrightarrow> a = Term\<close>
  by (cases a; simp add: less_eq_tres_def)+

lemma less_tres_eq[simp]:
  \<open>Term < a \<longleftrightarrow> a = Error\<close>
  \<open>a < Error \<longleftrightarrow> a = Term\<close>
  \<open>a < Term \<longleftrightarrow> False\<close>
  \<open>Error < a \<longleftrightarrow> False\<close>
  by (cases a; simp add: less_tres_def)+


subsubsection \<open> TRes has a Sup \<close>

instantiation tres :: sup
begin
definition \<open>sup_tres a b \<equiv> case a of Term \<Rightarrow> b | Error \<Rightarrow> Error\<close>
instance by standard
end

lemma sup_tres_eq[simp]:
  \<open>Error \<squnion> a = Error\<close>
  \<open>a \<squnion> Error = Error\<close>
  \<open>Term \<squnion> a = a\<close>
  \<open>a \<squnion> Term = a\<close>
  by (simp add: sup_tres_def split: tres.splits)+

instance tres :: semilattice_sup
  by standard (force simp add: sup_tres_def split: tres.splits)+


subsubsection \<open> TRes has an Inf \<close>

instantiation tres :: inf
begin
definition \<open>inf_tres a b \<equiv> case a of Error \<Rightarrow> b | Term \<Rightarrow> Term\<close>
instance by standard
end

lemma inf_tres_eq[simp]:
  \<open>Error \<sqinter> a = a\<close>
  \<open>a \<sqinter> Error = a\<close>
  \<open>Term \<sqinter> a = Term\<close>
  \<open>a \<sqinter> Term = Term\<close>
  by (simp add: inf_tres_def split: tres.splits)+

instance tres :: semilattice_inf
  by standard (force simp add: inf_tres_def split: tres.splits)+


subsubsection \<open> TRes has a Top \<close>

instantiation tres :: top
begin
definition \<open>top_tres \<equiv> Error\<close>
instance by standard
end

instance tres :: order_top
  by standard (simp add: top_tres_def)


subsubsection \<open> TRes has a Bot \<close>

instantiation tres :: bot
begin
definition \<open>bot_tres \<equiv> Term\<close>
instance by standard
end

instance tres :: order_bot
  by standard (simp add: bot_tres_def)


subsubsection \<open> TRes has a negation \<close>

instantiation tres :: uminus
begin
definition \<open>uminus_tres a \<equiv> case a of Term \<Rightarrow> Error | Error \<Rightarrow> Term\<close>
instance by standard
end

lemma uminus_tres_eq[simp]:
  \<open>- Error = Term\<close>
  \<open>- Term = Error\<close>
  by (simp add: uminus_tres_def)+


instantiation tres :: minus
begin
definition \<open>minus_tres (a::tres) b \<equiv> a \<sqinter> - b\<close>
instance by standard
end

lemma minus_tres_eq[simp]:
  \<open>Error - a = - a\<close>
  \<open>Term - a = Term\<close>
  \<open>a - Error = Term\<close>
  \<open>a - Term = a\<close>
  by (simp add: minus_tres_def)+


subsubsection \<open> TRes is a boolean algebra \<close>

instance tres :: lattice
  by standard

instance tres :: distrib_lattice
  by standard (simp add: inf_tres_def sup_tres_def split: tres.splits)

instance tres :: bounded_lattice
  by standard

instance tres :: boolean_algebra
  by standard
    (simp add: inf_tres_def bot_tres_def sup_tres_def top_tres_def split: tres.splits)+


subsection \<open> Commands \<close>

datatype 's comm =
  Done tres
  | Seq \<open>'s comm\<close> \<open>'s comm\<close> (infixr \<open>;;\<close> 75)
  | Par \<open>'s comm\<close> \<open>'s comm\<close> (infixr \<open>\<parallel>\<close> 65)
  | Indet \<open>'s comm\<close> \<open>'s comm\<close> (infixr \<open>\<^bold>\<sqinter>\<close> 65) \<comment> \<open> note the bold! \<close>
  | Endet \<open>'s comm\<close> \<open>'s comm\<close> (infixr \<open>\<^bold>\<box>\<close> 65) \<comment> \<open> note the bold! \<close>
  \<comment> \<open> An atomic action is represented by a precondition and a (relational) post-condition.
       Trying to evaluate the action outside the precondition results in a crash.
       Trying to evaluate the action outside the domain of the postcondition results in deadlock,
       until a state in the domain is reached. \<close>
  | Atomic \<open>'s \<Rightarrow> bool\<close> \<open>'s \<Rightarrow> 's \<Rightarrow> bool\<close> (\<open>\<langle>_, _\<rangle>\<close> [0,0] 1000)
  | Iter \<open>'s comm\<close> (\<open>DO _ OD\<close> [0] 999)

abbreviation \<open>Skip \<equiv> Done Term\<close>
abbreviation \<open>Crash \<equiv> Done Error\<close>


subsection \<open> substitution \<close>

subsection \<open> All Sub-commands \<close>

fun all_subcomm_eq :: \<open>'s comm \<Rightarrow> 's comm set\<close> where
  \<open>all_subcomm_eq (Done r) = {Done r}\<close>
| \<open>all_subcomm_eq (ca ;; cb) =
    insert (ca ;; cb) (all_subcomm_eq ca \<union> all_subcomm_eq cb)\<close>
| \<open>all_subcomm_eq (ca \<parallel> cb) =
    insert (ca \<parallel> cb) (all_subcomm_eq ca \<union> all_subcomm_eq cb)\<close>
| \<open>all_subcomm_eq (ca \<^bold>\<sqinter> cb) =
    insert (ca \<^bold>\<sqinter> cb) (all_subcomm_eq ca \<union> all_subcomm_eq cb)\<close>
| \<open>all_subcomm_eq (ca \<^bold>\<box> cb) =
    insert (ca \<^bold>\<box> cb) (all_subcomm_eq ca \<union> all_subcomm_eq cb)\<close>
| \<open>all_subcomm_eq (\<langle>p, q\<rangle>) = {\<langle>p, q\<rangle>}\<close>
| \<open>all_subcomm_eq (DO c OD) = insert (DO c OD) (all_subcomm_eq c)\<close>

fun all_subcomm :: \<open>'s comm \<Rightarrow> 's comm set\<close> where
  \<open>all_subcomm (Done r) = {}\<close>
| \<open>all_subcomm (ca ;; cb) = (all_subcomm_eq ca \<union> all_subcomm_eq cb)\<close>
| \<open>all_subcomm (ca \<parallel> cb) = (all_subcomm_eq ca \<union> all_subcomm_eq cb)\<close>
| \<open>all_subcomm (ca \<^bold>\<sqinter> cb) = (all_subcomm_eq ca \<union> all_subcomm_eq cb)\<close>
| \<open>all_subcomm (ca \<^bold>\<box> cb) = (all_subcomm_eq ca \<union> all_subcomm_eq cb)\<close>
| \<open>all_subcomm (\<langle>p, q\<rangle>) = {}\<close>
| \<open>all_subcomm (DO c OD) = (all_subcomm_eq c)\<close>


lemma all_subcomm_eq_eq:
  \<open>all_subcomm_eq c = insert c (all_subcomm c)\<close>
  by (induct c) force+

lemma all_subcomm_eq_trans:
  \<open>x \<in> all_subcomm_eq y \<Longrightarrow> y \<in> all_subcomm_eq z \<Longrightarrow> x \<in> all_subcomm_eq z\<close>
  by (induct z arbitrary: x y) force+

lemma all_subcomm_trans:
  \<open>x \<in> all_subcomm y \<Longrightarrow> y \<in> all_subcomm z \<Longrightarrow> x \<in> all_subcomm z\<close>
  by (induct z arbitrary: x y)
    (simp; metis all_subcomm_eq_eq insert_iff)+

lemma all_subcomm_all_subcomm_eq_trans:
  \<open>x \<in> all_subcomm y \<Longrightarrow> y \<in> all_subcomm_eq z \<Longrightarrow> x \<in> all_subcomm z\<close>
  by (induct z arbitrary: x y)
    (fastforce simp add: all_subcomm_eq_eq)+

lemma all_subcomm_eq_all_subcomm_trans:
  \<open>x \<in> all_subcomm_eq y \<Longrightarrow> y \<in> all_subcomm z \<Longrightarrow> x \<in> all_subcomm z\<close>
  by (induct z arbitrary: x y)
    (fastforce simp add: all_subcomm_eq_eq)+

lemma all_subcomm_irrefl:
  \<open>x \<notin> all_subcomm x\<close>
  apply (induct x)
        apply force
       apply (simp, metis UnCI all_subcomm.simps(2)
      all_subcomm_all_subcomm_eq_trans all_subcomm_eq_eq insertCI)
      apply (simp, metis UnCI all_subcomm.simps(3)
      all_subcomm_all_subcomm_eq_trans all_subcomm_eq_eq insertCI)
     apply (simp, metis UnCI all_subcomm.simps(4)
      all_subcomm_all_subcomm_eq_trans all_subcomm_eq_eq insertCI)
    apply (simp, metis UnCI all_subcomm.simps(5)
      all_subcomm_all_subcomm_eq_trans all_subcomm_eq_eq insertCI)
   apply force
  apply (simp, metis all_subcomm.simps(7)
      all_subcomm_all_subcomm_eq_trans all_subcomm_eq_eq insertCI)
  done

lemma in_all_subcomm_iff_in_allsubcomm_eq_neq:
  \<open>(x \<in> all_subcomm y) = (x \<in> all_subcomm_eq y \<and> x \<noteq> y)\<close>
  using all_subcomm_eq_eq all_subcomm_irrefl by blast

lemma all_subcomm_eq_loop_then_eq:
  \<open>x \<in> all_subcomm_eq y \<Longrightarrow> y \<in> all_subcomm_eq x \<Longrightarrow> x = y\<close>
  apply (induct y arbitrary: x)
        apply force
       apply (simp, metis UnCI all_subcomm.simps(2) all_subcomm_irrefl
      all_subcomm_all_subcomm_eq_trans)
      apply (simp, metis UnCI all_subcomm.simps(3) all_subcomm_irrefl
      all_subcomm_all_subcomm_eq_trans)
     apply (simp, metis UnCI all_subcomm.simps(4) all_subcomm_irrefl
      all_subcomm_all_subcomm_eq_trans)
    apply (simp, metis UnCI all_subcomm.simps(5) all_subcomm_irrefl
      all_subcomm_all_subcomm_eq_trans)
   apply force
  apply (simp, metis all_subcomm.simps(7) all_subcomm_irrefl
      all_subcomm_all_subcomm_eq_trans)
  done

lemma all_subcomm_no_loops:
  \<open>x \<in> all_subcomm y \<Longrightarrow> y \<in> all_subcomm x \<Longrightarrow> False\<close>
  using all_subcomm_irrefl all_subcomm_trans by blast


subsubsection \<open> Command ordering \<close>

instantiation comm :: (type) order
begin

definition less_eq_comm :: \<open>'a comm \<Rightarrow> 'a comm \<Rightarrow> bool\<close> where
  \<open>less_eq_comm x y \<equiv> \<exists>c\<in>all_subcomm_eq y. x = c\<close>

definition less_comm :: \<open>'a comm \<Rightarrow> 'a comm \<Rightarrow> bool\<close> where
  \<open>less_comm x y \<equiv> \<exists>c\<in>all_subcomm y. x = c\<close>

lemma less_comm_less_eq_comm_le_not:
  \<open>(x \<in> all_subcomm y) = (x \<in> all_subcomm_eq y \<and> y \<notin> all_subcomm_eq x)\<close>
  using all_subcomm_eq_all_subcomm_trans in_all_subcomm_iff_in_allsubcomm_eq_neq
  by blast

instance
  apply standard
     apply (simp add: less_comm_def less_comm_less_eq_comm_le_not
      less_eq_comm_def; fail)
    apply (simp add: all_subcomm_eq_eq less_eq_comm_def; fail)
   apply (simp add: less_eq_comm_def, metis all_subcomm_eq_trans)
  apply (simp add: less_eq_comm_def all_subcomm_eq_loop_then_eq; fail)
  done

end

lemma less_eq_comm_simps_right[simp]:
  \<open>c \<le> Done r \<longleftrightarrow> c = Done r\<close>
  \<open>c \<le> ca ;; cb \<longleftrightarrow> c = ca ;; cb \<or> c \<le> ca \<or> c \<le> cb\<close>
  \<open>c \<le> ca \<parallel> cb \<longleftrightarrow> c = ca \<parallel> cb \<or> c \<le> ca \<or> c \<le> cb\<close>
  \<open>c \<le> ca \<^bold>\<sqinter> cb \<longleftrightarrow> c = ca \<^bold>\<sqinter> cb \<or> c \<le> ca \<or> c \<le> cb\<close>
  \<open>c \<le> ca \<^bold>\<box> cb \<longleftrightarrow> c = ca \<^bold>\<box> cb \<or> c \<le> ca \<or> c \<le> cb\<close>
  \<open>c \<le> \<langle>p, q\<rangle> \<longleftrightarrow> c = \<langle>p, q\<rangle>\<close>
  \<open>c \<le> DO cx OD \<longleftrightarrow> c = DO cx OD \<or> c \<le> cx\<close>
  by (simp add: less_eq_comm_def)+

lemma less_comm_simps_right[simp]:
  \<open>c < Done r \<longleftrightarrow> False\<close>
  \<open>c < ca ;; cb \<longleftrightarrow> c \<le> ca \<or> c \<le> cb\<close>
  \<open>c < ca \<parallel> cb \<longleftrightarrow> c \<le> ca \<or> c \<le> cb\<close>
  \<open>c < ca \<^bold>\<sqinter> cb \<longleftrightarrow> c \<le> ca \<or> c \<le> cb\<close>
  \<open>c < ca \<^bold>\<box> cb \<longleftrightarrow> c \<le> ca \<or> c \<le> cb\<close>
  \<open>c < \<langle>p, q\<rangle> \<longleftrightarrow> False\<close>
  \<open>c < DO cx OD \<longleftrightarrow> c \<le> cx\<close>
  by (simp add: less_comm_def less_eq_comm_def)+

lemma less_eq_comm_leftD:
  \<open>ca ;; cb \<le> c \<Longrightarrow> ca \<le> c\<close>
  \<open>ca ;; cb \<le> c \<Longrightarrow> cb \<le> c\<close>
  \<open>ca \<parallel> cb \<le> c \<Longrightarrow> ca \<le> c\<close>
  \<open>ca \<parallel> cb \<le> c \<Longrightarrow> cb \<le> c\<close>
  \<open>ca \<^bold>\<sqinter> cb \<le> c \<Longrightarrow> ca \<le> c\<close>
  \<open>ca \<^bold>\<sqinter> cb \<le> c \<Longrightarrow> cb \<le> c\<close>
  \<open>ca \<^bold>\<box> cb \<le> c \<Longrightarrow> ca \<le> c\<close>
  \<open>ca \<^bold>\<box> cb \<le> c \<Longrightarrow> cb \<le> c\<close>
  \<open>DO cx OD \<le> c \<Longrightarrow> cx \<le> c\<close>
  by (meson order.refl order.trans less_eq_comm_simps_right; fail)+


subsection \<open> Atoms \<close>

subsection \<open> Map atomic commands \<close>

fun map_atom
  :: \<open>(('s \<Rightarrow> bool) \<Rightarrow> ('s \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow> ('u \<Rightarrow> bool) \<times> ('u \<Rightarrow> 'u \<Rightarrow> bool)) \<Rightarrow>
      's comm \<Rightarrow> 'u comm\<close>
  where
  \<open>map_atom f (Done r) = Done r\<close>
| \<open>map_atom f (a ;; b) = map_atom f a ;; map_atom f b\<close>
| \<open>map_atom f (a \<parallel> b) = map_atom f a \<parallel> map_atom f b\<close>
| \<open>map_atom f (a \<^bold>\<sqinter> b) = map_atom f a \<^bold>\<sqinter> map_atom f b\<close>
| \<open>map_atom f (a \<^bold>\<box> b) = map_atom f a \<^bold>\<box> map_atom f b\<close>
| \<open>map_atom f (Atomic p q) = case_prod Atomic (f p q)\<close>
| \<open>map_atom f (DO a OD) = DO map_atom f a OD\<close>

lemma map_atom_rev_iff:
  \<open>map_atom f c = Done r \<longleftrightarrow> c = Done r\<close>
  \<open>map_atom f c = c1' ;; c2' \<longleftrightarrow>
    (\<exists>c1 c2. c = c1 ;; c2 \<and> c1' = map_atom f c1 \<and> c2' = map_atom f c2)\<close>
  \<open>map_atom f c = c1' \<parallel> c2' \<longleftrightarrow>
      (\<exists>c1 c2. c = c1 \<parallel> c2 \<and> c1' = map_atom f c1 \<and> c2' = map_atom f c2)\<close>
  \<open>map_atom f c = c1' \<^bold>\<sqinter> c2' \<longleftrightarrow>
      (\<exists>c1 c2. c = c1 \<^bold>\<sqinter> c2 \<and> c1' = map_atom f c1 \<and> c2' = map_atom f c2)\<close>
  \<open>map_atom f c = c1' \<^bold>\<box> c2' \<longleftrightarrow>
      (\<exists>c1 c2. c = c1 \<^bold>\<box> c2 \<and> c1' = map_atom f c1 \<and> c2' = map_atom f c2)\<close>
  \<open>map_atom f c = DO c' OD \<longleftrightarrow>
      (\<exists>ca. c = DO ca OD \<and> c' = map_atom f ca)\<close>
  \<open>map_atom f c = Atomic p' q' \<longleftrightarrow>
      (\<exists>p q. f p q = (p', q') \<and> c = Atomic p q)\<close>
        apply (induct c; (simp add: fun_eq_iff split: prod.splits; argo)+)+
  apply (induct c; force split: prod.splits)
  done

lemmas map_atom_rev_iff2 = map_atom_rev_iff[THEN trans[OF eq_commute]]


fun all_atoms :: \<open>'s comm \<Rightarrow> (('s \<Rightarrow> bool) \<times> ('s \<Rightarrow> 's \<Rightarrow> bool)) multiset\<close> where
  \<open>all_atoms (Done r) = {#}\<close>
| \<open>all_atoms (ca ;; cb) = all_atoms ca + all_atoms cb\<close>
| \<open>all_atoms (ca \<parallel> cb) = all_atoms ca + all_atoms cb\<close>
| \<open>all_atoms (ca \<^bold>\<sqinter> cb) = all_atoms ca + all_atoms cb\<close>
| \<open>all_atoms (ca \<^bold>\<box> cb) = all_atoms ca + all_atoms cb\<close>
| \<open>all_atoms (\<langle>p, q\<rangle>) = {# (p,q) #}\<close>
| \<open>all_atoms (DO c OD) = all_atoms c\<close>


subsubsection \<open> All atom commands predicate \<close>

text \<open> Predicate to ensure atomic actions have a given property \<close>

definition all_atom_comm :: \<open>(('s \<Rightarrow> bool) \<Rightarrow> ('s \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow> bool) \<Rightarrow> 's comm \<Rightarrow> bool\<close> where
  \<open>all_atom_comm P c \<equiv> \<forall>p q. (p,q) \<in># all_atoms c \<longrightarrow> P p q\<close>

lemma all_atom_comm_simps[simp]:
  \<open>all_atom_comm P (Done r)\<close>
  \<open>all_atom_comm P (c1 ;; c2) \<longleftrightarrow> all_atom_comm P c1 \<and> all_atom_comm P c2\<close>
  \<open>all_atom_comm P (c1 \<^bold>\<sqinter> c2) \<longleftrightarrow> all_atom_comm P c1 \<and> all_atom_comm P c2\<close>
  \<open>all_atom_comm P (c1 \<^bold>\<box> c2) \<longleftrightarrow> all_atom_comm P c1 \<and> all_atom_comm P c2\<close>
  \<open>all_atom_comm P (c1 \<parallel> c2) \<longleftrightarrow> all_atom_comm P c1 \<and> all_atom_comm P c2\<close>
  \<open>all_atom_comm P (DO c OD) \<longleftrightarrow> all_atom_comm P c\<close>
  \<open>all_atom_comm P (Atomic ap aq) \<longleftrightarrow> P ap aq\<close>
  by (simp add: all_atom_comm_def all_conj_distrib)+

lemma all_atom_comm_pred_mono:
  \<open>P \<le> Q \<Longrightarrow> all_atom_comm P c \<Longrightarrow> all_atom_comm Q c\<close>
  unfolding all_atom_comm_def
  by force

lemma all_atom_comm_pred_mono':
  \<open>P \<le> Q \<Longrightarrow> all_atom_comm P \<le> all_atom_comm Q\<close>
  unfolding all_atom_comm_def
  by force

lemmas all_atom_comm_pred_monoD = all_atom_comm_pred_mono[rotated]

lemma all_atom_comm_conj_eq[simp]:
  \<open>all_atom_comm (P \<sqinter> Q) c \<longleftrightarrow> all_atom_comm P c \<and> all_atom_comm Q c\<close>
  unfolding all_atom_comm_def
  by force

lemma all_atom_comm_top_eq[simp]:
  \<open>all_atom_comm \<top> c\<close>
  unfolding all_atom_comm_def
  by force


subsection \<open> Head Atoms \<close>

fun head_atoms :: \<open>'s comm \<Rightarrow> (('s \<Rightarrow> bool) \<times> ('s \<Rightarrow> 's \<Rightarrow> bool)) multiset\<close> where
  \<open>head_atoms (Done r) = {#}\<close>
| \<open>head_atoms (ca ;; cb) = head_atoms ca\<close>
| \<open>head_atoms (ca \<parallel> cb) = (head_atoms ca + head_atoms cb)\<close>
| \<open>head_atoms (ca \<^bold>\<sqinter> cb) = {#}\<close>
| \<open>head_atoms (ca \<^bold>\<box> cb) = (head_atoms ca + head_atoms cb)\<close>
| \<open>head_atoms (\<langle>p, q\<rangle>) = {# (p,q) #}\<close>
| \<open>head_atoms (DO c OD) = head_atoms c\<close>

lemma head_atoms_subseteq_all_atoms:
  \<open>head_atoms c \<subseteq># all_atoms c\<close>
  by (induct c)
    (force simp add: subset_mset.add_increasing2 subset_mset.add_mono)+


subsection \<open> Atom Headed \<close>

text \<open>
  A predicate to determine if every executable subcommand in this command is an atom.
  (As opposed to a command like \<open>Done r; c\<close>.)
\<close>

fun head_atomic :: \<open>'s comm \<Rightarrow> bool\<close> where
  \<open>head_atomic (Done r) = False\<close>
| \<open>head_atomic (ca ;; cb) = head_atomic ca\<close>
| \<open>head_atomic (ca \<parallel> cb) = (head_atomic ca \<and> head_atomic cb)\<close>
| \<open>head_atomic (ca \<^bold>\<sqinter> cb) = False\<close>
| \<open>head_atomic (ca \<^bold>\<box> cb) = (head_atomic ca \<and> head_atomic cb)\<close>
| \<open>head_atomic (\<langle>p, q\<rangle>) = True\<close>
| \<open>head_atomic (DO c OD) = head_atomic c\<close>


section \<open> Specific Languages \<close>

subsection \<open> Sugared atomic programs \<close>

subsubsection \<open> Assert \<close>

definition \<open>Assert p \<equiv> Atomic p (=)\<close>

subsubsection \<open> Await \<close>

definition \<open>Await p \<equiv> Atomic \<top> (rel_liftL p \<sqinter> (=))\<close>

lemma Await_inject[simp]:
  \<open>Await p1 = Await p2 \<longleftrightarrow> p1 = p2\<close>
  by (force simp add: Await_def fun_eq_iff rel_lift_def)

subsection \<open> If-then-else \<close>

definition \<open>IfThenElse p ct cf \<equiv> Await p ;; ct \<^bold>\<box> Await (-p) ;; cf\<close>

lemma IfThenElse_inject[simp]:
  \<open>IfThenElse p1 ct1 cf1 = IfThenElse p2 ct2 cf2 \<longleftrightarrow> p1 = p2 \<and> ct1 = ct2 \<and> cf1 = cf2\<close>
  by (force simp add: IfThenElse_def fun_eq_iff)

lemma IfThenElse_distinct[simp]:
  \<open>IfThenElse p ct cf \<noteq> Done r\<close>
  \<open>IfThenElse p ct cf \<noteq> c1 ;; c2\<close>
  \<open>IfThenElse p ct cf \<noteq> c1 \<parallel> c2\<close>
  \<open>IfThenElse p ct cf \<noteq> Atomic ap aq\<close>
  \<open>Done r \<noteq> IfThenElse p ct cf\<close>
  \<open>c1 ;; c2 \<noteq> IfThenElse p ct cf\<close>
  \<open>c1 \<parallel> c2 \<noteq> IfThenElse p ct cf\<close>
  \<open>Atomic ap aq \<noteq> IfThenElse p ct cf\<close>
  by (simp add: IfThenElse_def)+


subsection \<open> WhileLoop \<close>

definition \<open>WhileLoop p c \<equiv> DO (Await p ;; c) OD\<close>

lemma WhileLoop_inject[simp]:
  \<open>WhileLoop p1 c1 = WhileLoop p2 c2 \<longleftrightarrow> p1 = p2 \<and> c1 = c2\<close>
  by (simp add: WhileLoop_def Await_def fun_eq_iff, blast)

lemma WhileLoop_distinct[simp]:
  \<open>WhileLoop p c \<noteq> Done r\<close>
  \<open>WhileLoop p c \<noteq> c1 \<^bold>\<box> c2\<close>
  \<open>WhileLoop p c \<noteq> c1 \<parallel> c2\<close>
  \<open>WhileLoop p c \<noteq> Atomic ap aq\<close>
  \<open>Done r \<noteq> WhileLoop p c\<close>
  \<open>c1 \<^bold>\<box> c2 \<noteq> WhileLoop p c\<close>
  \<open>c1 \<parallel> c2 \<noteq> WhileLoop p c\<close>
  \<open>Atomic ap aq \<noteq> WhileLoop p c\<close>
  by (simp add: WhileLoop_def; fail)+


section \<open> Logic Utils \<close>


section \<open> rely/guarantee helpers \<close>

abbreviation \<open>sswa r \<equiv> sp ((=) \<times>\<^sub>R r\<^sup>*\<^sup>*)\<close>
abbreviation \<open>wssa r \<equiv> wlp ((=) \<times>\<^sub>R r\<^sup>*\<^sup>*)\<close>

subsection \<open> rel relf + trans \<close>

lemma relyrel_trans: \<open>transp ((=) \<times>\<^sub>R r\<^sup>*\<^sup>*)\<close>
  by (metis rel_Times_left_eq_rtranclp_distrib transp_rtranclp)

lemma relyrel_mono: \<open>r1 \<le> r2 \<Longrightarrow> ((=) \<times>\<^sub>R r1\<^sup>*\<^sup>*) \<le> ((=) \<times>\<^sub>R r2\<^sup>*\<^sup>*)\<close>
  by (simp add: le_fun_def, metis mono_rtranclp)

subsection \<open> step properties \<close>

lemma sp_rely_step:
  \<open>r y y' \<Longrightarrow>
    sp ((=) \<times>\<^sub>R rx) p (x, y) \<Longrightarrow>
    sp ((=) \<times>\<^sub>R (rx OO r)) p (x, y')\<close>
  by (force simp add: sp_def)

lemma sswa_step:
  \<open>r y y' \<Longrightarrow>
    sswa r p (x, y) \<Longrightarrow>
    sswa r p (x, y')\<close>
  by (simp add: sp_def, meson rtranclp.rtrancl_into_rtrancl)

lemmas sswa_stepD = sswa_step[rotated]

lemma wssa_step:
  \<open>r y y' \<Longrightarrow>
    wssa r p (x, y) \<Longrightarrow>
    wssa r p (x, y')\<close>
  by (simp add: wlp_def converse_rtranclp_into_rtranclp)

lemmas wssa_stepD = wssa_step[rotated]

subsection \<open> closure operator properties \<close>

lemmas sswa_weaker = sp_refl_rel_le[where r=\<open>(=) \<times>\<^sub>R r\<^sup>*\<^sup>*\<close> for r, simplified]

lemma sswa_trivial[intro]:
  \<open>p x \<Longrightarrow> sswa r p x\<close>
  by (simp add: sp_refl_relI)

lemmas sswa_rel_mono = sp_rel_mono[OF relyrel_mono]

lemma wssa_trivial[dest]:
  \<open>wssa r p x \<Longrightarrow> p x\<close>
  by (drule wlp_refl_relD[rotated], simp)

lemmas wssa_stronger = wlp_refl_rel_le[where r=\<open>(=) \<times>\<^sub>R r\<^sup>*\<^sup>*\<close> for r, simplified]

lemmas wssa_rel_antimono = wlp_rel_antimono[OF relyrel_mono]


lemmas rely_rel_wlp_impl_sp =
  refl_rel_wlp_impl_sp[of \<open>(=) \<times>\<^sub>R r\<^sup>*\<^sup>*\<close> \<open>(=) \<times>\<^sub>R r\<^sup>*\<^sup>*\<close> for r, simplified]


subsection \<open> absorption/pseduo-idempotence properties \<close>

(*
lemmas sswa_idem[simp] =
  sp_comp_rel[where ?r1.0=\<open>(=) \<times>\<^sub>R r\<^sup>*\<^sup>*\<close> and ?r2.0=\<open>(=) \<times>\<^sub>R r\<^sup>*\<^sup>*\<close> for r, simplified]

lemmas wssa_idem[simp] =
  wlp_comp_rel[where ?r1.0=\<open>(=) \<times>\<^sub>R r\<^sup>*\<^sup>*\<close> and ?r2.0=\<open>(=) \<times>\<^sub>R r\<^sup>*\<^sup>*\<close> for r, simplified]
*)

lemma sswa_over_sswa_eq[simp]:
  \<open>r1 \<le> r2 \<Longrightarrow> sswa r1 (sswa r2 p) = sswa r2 p\<close>
  by (simp add: rel_le_rtranscp_relcompp_absorb(1) sp_comp_rel)

lemma wssa_over_wssa_eq[simp]:
  \<open>r1 \<le> r2 \<Longrightarrow> wssa r1 (wssa r2 p) = wssa r2 p\<close>
  by (simp add: rel_le_rtranscp_relcompp_absorb(2) wlp_comp_rel)

lemma sswa_over_wssa_eq[simp]:
  \<open>r1 \<le> r2 \<Longrightarrow> sswa r1 (wssa r2 p) = wssa r2 p\<close>
  by (force simp add: relyrel_trans relyrel_mono sp_wlp_absorb)

lemma wssa_over_sswa_eq[simp]:
  \<open>r1 \<le> r2 \<Longrightarrow> wssa r1 (sswa r2 p) = sswa r2 p\<close>
  by (simp add: relyrel_mono relyrel_trans wlp_sp_absorb)


subsection \<open> semi-distributivity with sepconj-conj \<close>

lemma wlp_rely_sepconj_conj_semidistrib_mono:
  \<open>p' \<le> wlp ((=) \<times>\<^sub>R r) p \<Longrightarrow>
    q' \<le> wlp ((=) \<times>\<^sub>R r) q \<Longrightarrow>
    p' \<^emph>\<and> q' \<le> wlp ((=) \<times>\<^sub>R r) (p \<^emph>\<and> q)\<close>
  by (fastforce simp add: wlp_def sepconj_conj_def le_fun_def)

lemmas wlp_rely_sepconj_conj_semidistrib =
  wlp_rely_sepconj_conj_semidistrib_mono[OF order.refl order.refl]

lemma sp_rely_sepconj_conj_semidistrib_mono:
  \<open>sp ((=) \<times>\<^sub>R r) p \<le> p' \<Longrightarrow>
    sp ((=) \<times>\<^sub>R r) q \<le> q' \<Longrightarrow>
    sp ((=) \<times>\<^sub>R r) (p \<^emph>\<and> q) \<le> p' \<^emph>\<and> q'\<close>
  by (fastforce simp add: sp_def sepconj_conj_def le_fun_def)

lemmas sp_rely_sepconj_conj_semidistrib =
  sp_rely_sepconj_conj_semidistrib_mono[OF order.refl order.refl]

subsection \<open> Interaction with pred-Times \<close>

lemma wssa_of_pred_Times_eq[simp]:
  \<open>wssa r (p \<times>\<^sub>P q) = (p \<times>\<^sub>P wlp r\<^sup>*\<^sup>* q)\<close>
  by (force simp add: rel_Times_def pred_Times_def wlp_def split: prod.splits)

lemma sp_rely_of_pred_Times_eq[simp]:
  \<open>sswa r (p \<times>\<^sub>P q) = (p \<times>\<^sub>P sp r\<^sup>*\<^sup>* q)\<close>
  by (force simp add: rel_Times_def pred_Times_def sp_def split: prod.splits)


subsection \<open> Local and shared predicate lifting \<close>

abbreviation(input) local_pred
  :: \<open>('a \<Rightarrow> bool) \<Rightarrow> ('a \<times> 'b \<Rightarrow> bool)\<close> (\<open>\<L>\<close>)
  where
    \<open>\<L>(p) \<equiv> p \<circ> fst\<close>

abbreviation(input) shared_pred
  :: \<open>('b \<Rightarrow> bool) \<Rightarrow> ('a \<times> 'b \<Rightarrow> bool)\<close> (\<open>\<S>\<close>)
  where
    \<open>\<S>(p) \<equiv> p \<circ> snd\<close>

lemma wssa_ignore_local[simp]:
  \<open>wssa r (\<L> pl) = \<L> pl\<close>
  by (fastforce simp add: wlp_def fun_eq_iff sepconj_conj_def)

lemma sswa_ignore_local[simp]:
  \<open>sswa r (\<L> pl) = \<L> pl\<close>
  \<open>sswa r (\<L> pl \<^emph>\<and> q) = \<L> pl \<^emph>\<and> sswa r q\<close>
  \<open>sswa r (p \<^emph>\<and> \<L> ql) = sswa r p \<^emph>\<and> \<L> ql\<close>
  by (force simp add: sp_def fun_eq_iff sepconj_conj_def)+

lemma wssa_over_shared:
  \<open>wssa r (\<S> ps) = \<S> (wlp r\<^sup>*\<^sup>* ps)\<close>
  by (force simp add: wlp_def fun_eq_iff sepconj_conj_def)

lemma sswa_over_shared:
  \<open>sswa r (\<S> ps) = \<S> (sp r\<^sup>*\<^sup>* ps)\<close>
  by (force simp add: sp_def fun_eq_iff sepconj_conj_def)

lemma wssa_semiignore_local[simp]:
  \<open>\<L> pl \<^emph>\<and> wssa r q \<le> wssa r (\<L> pl \<^emph>\<and> q)\<close>
  \<open>wssa r p \<^emph>\<and> \<L> ql \<le> wssa r (p \<^emph>\<and> \<L> ql)\<close>
  by (force simp add: wlp_def fun_eq_iff sepconj_conj_def)+

text \<open>
  The full law local ignore law is _not_ true for \<open>wssa\<close>, unlike the one for \<open>sswa\<close>.
  Imagine the following situation:
    State model: \<open>bool \<times> bool\<close>
    Sep-algebra: \<open>R000, R011, R101, R111\<close>
    Inputs:
      \<open>q = {11, 00}\<close>
      \<open>r = (0 \<leadsto> 1, 0 \<leadsto> 1)\<close>
    Results:
      \<open>wssa r q = {}\<close>
      \<open>\<L> \<top> \<^emph>\<and> q = {11, 10, 00}\<close>
      \<open>(\<L> pl \<^emph>\<and> wssa r q) = {}\<close>
      \<open>wssa r (\<L> pl \<^emph>\<and> q) = {11, 10}\<close>
    Here we observe that the outputs are not the same, because \<open>wssa\<close> only preserves
    a \<^emph>\<open>subset\<close> of the initial predicate, and this subset might not be compatible
    with the frame.
\<close>

lemma sepconj_local_eq:
  \<open>\<L> p \<^emph>\<and> \<L> q = \<L> (p \<^emph> q)\<close>
  by (simp add: sepconj_conj_def sepconj_def fun_eq_iff)

lemma sepconj_shared_eq:
  \<open>(\<S> p :: 'a::multiunit_sep_alg \<times> 'b \<Rightarrow> bool) \<^emph>\<and> \<S> q = \<S> (p \<sqinter> q)\<close>
  by (force simp add: sepconj_conj_def sepconj_def fun_eq_iff)


end
