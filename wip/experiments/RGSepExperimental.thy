theory RGSepExperimental
  imports "../Soundness"
begin


lemma safe_refinement_mono:
  \<open>safe n prg hl hs r g q F \<Longrightarrow> prg = (Atomic b') \<Longrightarrow> b \<le> b' \<Longrightarrow> safe n (Atomic b) hl hs r g q F\<close>
  apply (induct arbitrary: b' b rule: safe.inducts)
   apply force
  apply (simp add: safe_sucE)
  apply (rule safe_suc)
      apply blast
     apply blast
    apply (clarsimp simp add: opstep_iff le_fun_def, metis)
   apply (clarsimp simp add: opstep_iff le_fun_def; fail)
  apply (clarsimp simp add: opstep_iff le_fun_def; fail)  
  done


lemma
  fixes p :: \<open>'a::perm_alg \<times> 'b::perm_alg \<Rightarrow> bool\<close>
    and Pa :: \<open>'a \<Rightarrow> 'a \<Rightarrow> 'a option\<close>
    and Pb :: \<open>'b \<Rightarrow> 'b \<Rightarrow> 'b option\<close>
  shows \<open>
    \<forall>f. sp b (p \<^emph>\<and> f) \<le> (q1 \<^emph>\<and> f) \<Longrightarrow>
    \<forall>f. sp b (p \<^emph>\<and> f) \<le> (q2 \<^emph>\<and> f) \<Longrightarrow>
    \<forall>y c c'. b (Err, c) (y, c') \<longrightarrow> y = Err \<Longrightarrow>
    \<forall>x y z::'a. x + z = y + z \<longrightarrow> z \<noteq> Err \<longrightarrow> x = y \<Longrightarrow>
    \<forall>x y::'a. x ## y \<Longrightarrow>
    \<forall>x y::'b. x ## y \<Longrightarrow>
    \<forall>x y. Pa x y = (if x ## y then Some (x + y) else None) \<Longrightarrow>
    \<forall>x y. Pb x y = (if x ## y then Some (x + y) else None) \<Longrightarrow>
    sp b (p \<^emph>\<and> f) \<le> ((q1 \<sqinter> q2) \<^emph>\<and> f)
  \<close>
  nitpick[card 'b=1]
  oops

definition perm_alg_homomorphism :: \<open>('a :: perm_alg \<Rightarrow> 'b :: perm_alg) \<Rightarrow> bool\<close> where
  \<open>perm_alg_homomorphism f \<equiv>
    (\<forall>x y. x ## y \<longrightarrow> f x ## f y) \<and>
    (\<forall>x y. x ## y \<longrightarrow> f (x + y) = f x + f y)\<close>

definition sep_alg_homomorphism :: \<open>('a :: sep_alg \<Rightarrow> 'b :: sep_alg) \<Rightarrow> bool\<close> where
  \<open>sep_alg_homomorphism f \<equiv>
    (\<forall>x y. x ## y \<longrightarrow> f x ## f y) \<and>
    (\<forall>x y. x ## y \<longrightarrow> f (x + y) = f x + f y) \<and>
    (\<forall>x. f (unitof x) = unitof (f x)) \<and>
    (f 0 = 0)\<close>


lemma perm_alg_homomorphism_mono:
  \<open>perm_alg_homomorphism f \<Longrightarrow> x \<preceq> y \<Longrightarrow> f x \<preceq> f y\<close>
  by (clarsimp simp add: less_eq_sepadd_def' perm_alg_homomorphism_def, metis)

lemma perm_alg_homomorphism_tuple:
  \<open>perm_alg_homomorphism f \<Longrightarrow>
    perm_alg_homomorphism g \<Longrightarrow>
    perm_alg_homomorphism (map_prod f g)\<close>
  by (clarsimp simp add: perm_alg_homomorphism_def)

definition
  \<open>split_preserving_morphism (f :: ('a::perm_alg \<Rightarrow> 'b::perm_alg)) \<equiv>
    \<forall>x y' z'. y' ## z' \<longrightarrow> f x = y' + z' \<longrightarrow> (\<exists>y z. x = y + z \<and> y ## z \<and> y' = f y \<and> z' = f z)\<close>

lemma function_rel_subsetD:
  \<open>(\<lambda>x y. r (f x) (f y))\<^sup>*\<^sup>* x y \<Longrightarrow> (\<lambda>x y. r\<^sup>*\<^sup>* (f x) (f y)) x y\<close>
  by (induct rule: rtranclp_induct) force+

lemma function_rel_subset:
  \<open>(\<lambda>x y. r (f x) (f y))\<^sup>*\<^sup>* \<le> (\<lambda>x y. r\<^sup>*\<^sup>* (f x) (f y))\<close>
  by (simp add: function_rel_subsetD predicate2I)

lemma helper:
  \<open>sswa (\<lambda>a b. r (fs a) (fs b)) (i \<circ> map_prod fl fs) \<le> (\<lambda>a. sswa r i (map_prod fl fs a))\<close>
  apply (clarsimp simp add: sp_def fun_eq_iff)
  apply (rename_tac a y x)
  apply (rule_tac x=\<open>fs x\<close> in exI)
  apply (rule conjI)
   apply (simp add: function_rel_subsetD; fail)
  apply blast
  done

definition rel_precomp :: \<open>('a \<Rightarrow> 'a \<Rightarrow> 'z) \<Rightarrow> ('b \<Rightarrow> 'a) \<Rightarrow> ('b \<Rightarrow> 'b \<Rightarrow> 'z)\<close> (infixl \<open>\<circ>\<^sub>R\<close> 55) where
  \<open>r \<circ>\<^sub>R f \<equiv> \<lambda>x y. r (f x) (f y)\<close>

lemma rel_precomp_sup_eq:
  \<open>(r1 \<squnion> r2) \<circ>\<^sub>R f = (r1 \<circ>\<^sub>R f) \<squnion> (r2 \<circ>\<^sub>R f)\<close>
  by (fastforce simp add: rel_precomp_def)

lemma helper_rewrite:
  \<open>\<forall>x y. (\<lambda>x y. r (fs x) (fs y))\<^sup>*\<^sup>* = (\<lambda>x y. r\<^sup>*\<^sup>* (fs x) (fs y)) \<Longrightarrow>
    range fs = UNIV \<Longrightarrow>
    sswa r p \<circ> map_prod fl fs = sswa (r \<circ>\<^sub>R fs) (p \<circ> map_prod fl fs)\<close>
  apply (clarsimp simp add: sp_def comp_def rel_precomp_def fun_eq_iff)
  apply (rule iffI)
   apply (metis surjD)
  apply blast
  done

lemma rel_precomp_mono:
  \<open>r \<le> r' \<Longrightarrow> r \<circ>\<^sub>R fs \<le> r' \<circ>\<^sub>R fs\<close>
  by (simp add: le_fun_def rel_precomp_def)

lemma sepconj_conj_map_prod_impl1:
  \<open>perm_alg_homomorphism fl \<Longrightarrow>
    ((q1' \<circ> map_prod fl fs) \<^emph>\<and> (q2' \<circ> map_prod fl fs)) x \<Longrightarrow>
    (q1' \<^emph>\<and> q2') (map_prod fl fs x)\<close>
  apply (clarsimp simp add: sepconj_conj_def perm_alg_homomorphism_def)
  apply blast
  done

lemma
  \<open>perm_alg_homomorphism (f :: ('a::perm_alg \<Rightarrow> 'b::perm_alg)) \<Longrightarrow>
    \<forall>x. f x ## f x \<longrightarrow> x ## x \<Longrightarrow>
    \<forall>x. sepadd_unit (f x) \<longrightarrow> sepadd_unit x \<Longrightarrow>
    \<forall>x y. (x ## y \<longrightarrow> pa x y = Some (x + (y::'a))) \<and> (\<not>x ## y \<longrightarrow> pa x y = None) \<Longrightarrow>
    \<forall>x y. (x ## y \<longrightarrow> pb x y = Some (x + (y::'b))) \<and> (\<not>x ## y \<longrightarrow> pb x y = None) \<Longrightarrow>
    \<forall>x y' z'. y' ## z' \<longrightarrow> f x = y' + z' \<longrightarrow> (\<exists>y z. x = y + z \<and> y ## z \<and> y' = f y \<and> z' = f z)\<close>
  apply (clarsimp simp add: sep_alg_homomorphism_def)
  oops

lemma sepconj_conj_map_prod_eq:
  \<open>perm_alg_homomorphism fl \<Longrightarrow>
    split_preserving_morphism fl \<Longrightarrow>
    (q1' \<^emph>\<and> q2') (map_prod fl fs a) = ((q1' \<circ> map_prod fl fs) \<^emph>\<and> (q2' \<circ> map_prod fl fs)) a\<close>
  apply (cases a)
  apply (clarsimp simp add: sepconj_conj_def perm_alg_homomorphism_def
      split_preserving_morphism_def)
  apply (rule iffI, blast, metis)
  done


lemma semilattice_sup_helper1:
  fixes ra :: \<open>'a :: semilattice_sup\<close>
  shows
  \<open>rb1 \<le> rb \<Longrightarrow>
    rb2 \<le> rb \<Longrightarrow>
    ra \<le> rab' \<Longrightarrow>
    rb2 \<le> rab' \<Longrightarrow>
    rab' \<le> ra \<squnion> rb2 \<squnion> rb1 \<Longrightarrow>
    rab' \<le> ra \<squnion> rb\<close>
  by (metis sup.absorb_iff2 sup_assoc)

lemma rgsat_preserved_under_homomorphism:
  fixes p :: \<open>'a::perm_alg \<times> 'b::perm_alg \<Rightarrow> bool\<close>
    and q :: \<open>'a \<times> 'b \<Rightarrow> bool\<close>
    and fl :: \<open>'c::perm_alg \<Rightarrow> 'a\<close>
    and fs :: \<open>'d::perm_alg \<Rightarrow> 'b\<close>
  shows
  \<open>rgsat c r g p q \<Longrightarrow>
    perm_alg_homomorphism fl \<Longrightarrow>
    perm_alg_homomorphism fs \<Longrightarrow>
    split_preserving_morphism fl \<Longrightarrow>
    (\<And>p rx. r \<le> rx \<Longrightarrow> rx \<le> r \<squnion> g \<Longrightarrow>
        sswa rx p \<circ> map_prod fl fs = sswa (rx \<circ>\<^sub>R fs) (p \<circ> map_prod fl fs)) \<Longrightarrow>
    c' = map_comm (map_prod fl fs) c \<Longrightarrow>
    p' = (p \<circ> map_prod fl fs) \<Longrightarrow>
    q' = (q \<circ> map_prod fl fs) \<Longrightarrow>
    r' = r \<circ>\<^sub>R fs \<Longrightarrow>
    g' = g \<circ>\<^sub>R fs \<Longrightarrow>
    rgsat c' r' g' p' q'\<close>
proof (induct arbitrary: c' p' q' r' g' rule: rgsat.inducts)
  case (rgsat_skip r p q g)
  then show ?case
    apply (clarsimp simp add: map_comm_rev_iff2)
    apply (rule rgsat.rgsat_skip)
    apply (clarsimp simp add: le_fun_def sp_def imp_ex_conjL rel_precomp_def)
    apply (frule function_rel_subsetD)
    apply blast
    done
next
  case (rgsat_iter c r g i p q)
  show ?case
    using rgsat_iter.prems rgsat_iter.hyps(1,3-)
    apply (clarsimp simp add: map_comm_rev_iff2 simp del: sup_apply)
    apply (rule rgsat.rgsat_iter[where i=\<open>i \<circ> map_prod fl fs\<close>])
      apply (rule rgsat_iter.hyps(2); simp add: comp_def sp_comp_rel del: sup_apply; fail)
     apply fastforce
    apply (drule meta_spec[of _ r])
    apply (clarsimp simp add: le_fun_def comp_def)
    apply (metis map_prod_simp)
    done
next
  case (rgsat_seq c1 r g p1 p2 c2 p3)
  show ?case
    using rgsat_seq.prems
    apply (clarsimp simp add: map_comm_rev_iff2)
    apply (rule rgsat.rgsat_seq)
     apply (rule rgsat_seq.hyps(2); force simp add: comp_def sp_comp_rel)
    apply (rule rgsat_seq.hyps(4); simp add: comp_def sp_comp_rel; fail)
    done
next
  case (rgsat_indet c1 r g1 p q1 c2 g2 q2 g q)
  show ?case
    using rgsat_indet.prems rgsat_indet.hyps(5-)
    apply (clarsimp simp add: map_comm_rev_iff2 simp del: sup_apply)
    apply (rule rgsat.rgsat_indet)
         apply (rule rgsat_indet.hyps(2); simp add: comp_def sp_comp_rel del: sup_apply)
         apply (drule_tac x=rx in meta_spec)
         apply (simp del: sup_apply, blast)
        apply (rule rgsat_indet.hyps(4); simp add: comp_def sp_comp_rel)
        apply (drule_tac x=rx in meta_spec)
        apply (simp del: sup_apply, blast)
       apply (metis rel_precomp_mono)
      apply (metis rel_precomp_mono)
     apply (simp add: le_fun_def)
    apply (simp add: le_fun_def)
    done
next
  case (rgsat_endet c1 r g1 p q1 c2 g2 q2 g q)
  show ?case
    using rgsat_endet.prems rgsat_endet.hyps(5-)
    apply (clarsimp simp add: map_comm_rev_iff2)
    apply (rule rgsat.rgsat_endet)
         apply (rule rgsat_endet.hyps(2); simp add: comp_def sp_comp_rel)
         apply (drule_tac x=rx in meta_spec)
         apply (simp del: sup_apply, blast)
        apply (rule rgsat_endet.hyps(4); simp add: comp_def sp_comp_rel)
        apply (drule_tac x=rx in meta_spec)
        apply (simp del: sup_apply, blast)
       apply (metis rel_precomp_mono)
      apply (metis rel_precomp_mono)
     apply (simp add: le_fun_def)
    apply (simp add: le_fun_def)
    done
next
  case (rgsat_par s1 r g2 g1 p1 q1 s2 p2 q2 g p q)
  show ?case
    using rgsat_par.prems rgsat_par.hyps(5-)
    apply (clarsimp simp add: map_comm_rev_iff2 sepconj_conj_map_prod_eq simp del: sup_apply)
    apply (rule rgsat.rgsat_par[of
          _ \<open>r \<circ>\<^sub>R fs\<close> \<open>g2 \<circ>\<^sub>R fs\<close> \<open>g1 \<circ>\<^sub>R fs\<close> \<open>p1 \<circ> map_prod fl fs\<close> \<open>q1 \<circ> map_prod fl fs\<close>
          _ \<open>p2 \<circ> map_prod fl fs\<close> \<open>q2 \<circ> map_prod fl fs\<close>])
         apply (rule rgsat_par.hyps(2); (simp del: sup_apply)?) (* 6 \<rightarrow> 7 *)
          apply (metis semilattice_sup_helper1)
         apply (metis rel_precomp_sup_eq)
        apply (rule rgsat_par.hyps(4); (simp del: sup_apply)?) (* 6 \<rightarrow> 7 *)
         apply (metis semilattice_sup_helper1)
        apply (metis rel_precomp_sup_eq)
       apply (simp add: rel_precomp_mono; fail)
      apply (simp add: rel_precomp_mono; fail)
     apply (drule_tac x=\<open>r \<squnion> g2\<close> and y=q1 in meta_spec2)
     apply (clarsimp simp add: rel_precomp_sup_eq[symmetric] le_supI2 comp_def simp del: sup_apply)
     apply (clarsimp simp add: le_fun_def sepconj_conj_def split_preserving_morphism_def, metis)
    apply (drule_tac x=\<open>r \<squnion> g1\<close> and y=q2 in meta_spec2)
    apply (clarsimp simp add: rel_precomp_sup_eq[symmetric] le_supI2 comp_def simp del: sup_apply)
    apply (clarsimp simp add: le_fun_def sepconj_conj_def split_preserving_morphism_def)
    apply (rename_tac s l1 l2)
    sorry
next
  case (rgsat_atom b r p q g p' q')
  then show ?case
    apply (clarsimp simp add: map_comm_rev_iff2 sepconj_conj_map_prod_eq)
    apply (rule rgsat.rgsat_atom)
    sorry
next
  case (rgsat_frame c r g p q f f')
  then show ?case sorry
next
  case (rgsat_weaken c rx gx px qx p q r g)
  show ?case
    using rgsat_weaken.prems rgsat_weaken.hyps(3-)
    apply -
    apply (rule rgsat.rgsat_weaken[of _
          \<open>rx \<circ>\<^sub>R fs\<close> \<open>gx \<circ>\<^sub>R fs\<close> \<open>px \<circ> map_prod fl fs\<close> \<open>qx \<circ> map_prod fl fs\<close>])
        apply (rule rgsat_weaken.hyps(2); simp)
    oops


lemma rgsat_preserved_under_homomorphism2:
  fixes p :: \<open>'a::perm_alg \<times> 'b::perm_alg \<Rightarrow> bool\<close>
    and q :: \<open>'a \<times> 'b \<Rightarrow> bool\<close>
    and fl :: \<open>'c::perm_alg \<Rightarrow> 'a\<close>
    and fs :: \<open>'d::perm_alg \<Rightarrow> 'b\<close>
  shows
  \<open>rgsat c' r' g' p' q' \<Longrightarrow>
    perm_alg_homomorphism fl \<Longrightarrow>
    perm_alg_homomorphism fs \<Longrightarrow>
    (\<And>p. sswa r p \<circ> map_prod fl fs = sswa (r \<circ>\<^sub>R fs) (p \<circ> map_prod fl fs)) \<Longrightarrow>
    surj fl \<Longrightarrow>
    surj fs \<Longrightarrow>
    c' = map_comm (map_prod fl fs) c \<Longrightarrow>
    p' = (p \<circ> map_prod fl fs) \<Longrightarrow>
    q' = (q \<circ> map_prod fl fs) \<Longrightarrow>
    r' = r \<circ>\<^sub>R fs \<Longrightarrow>
    g' = g \<circ>\<^sub>R fs \<Longrightarrow>
    rgsat c r g p q\<close>
  oops


end