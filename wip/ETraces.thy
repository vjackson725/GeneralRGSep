theory ETraces
  imports "../Security"
begin


subsubsection \<open> Reverse Aopsteps \<close>

inductive aopsteps_rev
  :: \<open>_ list \<Rightarrow>
      ('l \<times> 's) \<times> ('l \<times> 's) comm \<Rightarrow>
      ('l \<times> 's) \<times> ('l \<times> 's) comm \<Rightarrow>
      bool\<close>
  where
  aopsteps_rev_nil[intro!]:
  \<open>sc'' = sc \<Longrightarrow> aopsteps_rev [] sc sc''\<close>
| aopsteps_rev_cons[intro!]:
  \<open>aopsteps_rev \<rho> sc sc' \<Longrightarrow>
    aopstep \<alpha> sc' sc'' \<Longrightarrow>
    aopsteps_rev (\<rho> @ [\<alpha>]) sc sc''\<close>

lemmas aopsteps_rev_singletonI[intro!] = aopsteps_rev_cons[of \<open>[]\<close>, OF aopsteps_rev_nil, simplified]

inductive_cases aopsteps_rev_nilE[elim!]: \<open>aopsteps_rev [] sc sc'\<close>
inductive_cases aopsteps_rev_rconsE[elim!]: \<open>aopsteps_rev (\<rho>e @ [\<alpha>e]) sc sc'\<close>

abbreviation aopsteps_rev_pretty :: \<open>_ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> bool\<close> (\<open>_ \<midarrow>_\<rightarrow>\<^sub>a\<^sub>r\<^sup>* _\<close> [50, 0, 50]) where
  \<open>sc \<midarrow>\<rho>e\<rightarrow>\<^sub>a\<^sub>r\<^sup>* sc' \<equiv> aopsteps_rev \<rho>e sc sc'\<close>

lemma aopsteps_rev_simps[simp]:
  \<open>aopsteps_rev [] sc sc' \<longleftrightarrow> sc' = sc\<close>
  \<open>aopsteps_rev (\<rho>e @ [\<alpha>e]) sc sc'' \<longleftrightarrow>
    (\<exists>sc'. aopsteps_rev \<rho>e sc sc' \<and> aopstep \<alpha>e sc' sc'')\<close>
  by force+

paragraph \<open> Aopsteps-rev to Aopsteps \<close>

lemma aopsteps_rev_aopsteps_to_aopsteps:
  \<open>aopsteps_rev \<rho>x sc sc' \<Longrightarrow>
    aopsteps \<rho>y sc' sc'' \<Longrightarrow>
    aopsteps (\<rho>x @ \<rho>y) sc sc''\<close>
  apply (induct arbitrary: \<rho>y sc'' rule: aopsteps_rev.induct)
   apply force
  apply (clarsimp, blast)
  done

lemma aopsteps_rev_to_aopsteps:
  \<open>aopsteps_rev \<rho> sc sc' \<Longrightarrow> aopsteps \<rho> sc sc'\<close>
  using aopsteps_rev_aopsteps_to_aopsteps[where \<rho>y=\<open>[]\<close> and sc'=sc' and sc''=sc', simplified]
  by (case_tac sc', simp)

paragraph \<open> Aopsteps to Aopsteps-rev \<close>

lemma aopsteps_rev_aopsteps_to_aopsteps_rev:
  \<open>aopsteps \<rho>y sc' sc'' \<Longrightarrow>
    aopsteps_rev \<rho>x sc sc' \<Longrightarrow>
    aopsteps_rev (\<rho>x @ \<rho>y) sc sc''\<close>
  by (induct arbitrary: \<rho>x rule: aopsteps.induct) force+

lemma aopsteps_to_aopsteps_rev:
  \<open>aopsteps \<rho> sc sc' \<Longrightarrow> aopsteps_rev \<rho> sc sc'\<close>
  using aopsteps_rev_aopsteps_to_aopsteps_rev[where \<rho>x=\<open>[]\<close> and sc=sc and sc''=sc', simplified]
  by auto

\<comment> \<open> TODO: remove \<close>
section \<open> Extended step \<close>

datatype 'a eact =
  Env
  | Loc \<open>'a\<close>

lemma map_eact_rev[simp]:
  \<open>map_eact f \<alpha>e = Env \<longleftrightarrow> \<alpha>e = Env\<close>
  \<open>map_eact f \<alpha>e = Loc \<alpha> \<longleftrightarrow> (\<exists>\<alpha>'. \<alpha>e = Loc \<alpha>' \<and> \<alpha> = f \<alpha>')\<close>
  by (cases \<alpha>e; force)+

lemmas map_eact_rev'[simp] = map_eact_rev[THEN trans[rotated], OF eq_commute]


definition
  \<open>estep step R F \<equiv>
    \<lambda>\<alpha>e. case \<alpha>e of
      Env \<Rightarrow>
        (\<lambda>sc sc'.
          snd sc' = snd sc \<and>
          fst (fst sc') = fst (fst sc) \<and>
          R (snd (fst sc)) (snd (fst sc')) \<and>
          (\<exists>f. F (f, snd (fst sc)) \<and> fst (fst sc) ## f) \<and>
          (\<exists>f. F (f, snd (fst sc')) \<and> fst (fst sc') ## f))
      | Loc \<alpha> \<Rightarrow>
        (\<lambda>((sl, ss), c) ((sl', ss'), c').
          \<exists>f.
            F (f, ss) \<and>
            sl ## f \<and>
            F (f, ss') \<and>
            sl' ## f \<and>
            step \<alpha> ((sl + f, ss), c) ((sl' + f, ss'), c'))\<close>


paragraph \<open> Pretty extended extended opsem \<close>

abbreviation pretty_estep :: \<open>_ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> bool\<close> (\<open>_ \<midarrow>_, _, _\<rightarrow>\<^sub>e _\<close> [60,0,0,0,60] 60) where
  \<open>sc \<midarrow>r, F, \<gamma>\<rightarrow>\<^sub>e sc' \<equiv> estep opstep r F \<gamma> sc sc'\<close>

abbreviation pretty_no_estep :: \<open>_ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> bool\<close> (\<open>_ \<midarrow>_, _ '/\<rightarrow>\<^sub>e\<close> [60, 0, 0] 60) where
  \<open>sc \<midarrow>r, F /\<rightarrow>\<^sub>e \<equiv> \<forall>\<gamma>. \<forall>sc'::_\<times>_. \<not> estep opstep r F \<gamma> sc sc'\<close>

abbreviation pretty_eastep :: \<open>_ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> bool\<close> (\<open>_ \<midarrow>_, _, _\<rightarrow>\<^sub>e\<^sub>a _\<close> [60,0,0,0,60] 60) where
  \<open>sc \<midarrow>r, F, \<gamma>\<rightarrow>\<^sub>e\<^sub>a sc' \<equiv> estep aopstep r F \<gamma> sc sc'\<close>

abbreviation prsetty_no_eastep :: \<open>_ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> bool\<close> (\<open>_ \<midarrow>_, _ '/\<rightarrow>\<^sub>e\<^sub>a\<close> [60, 0, 0] 60) where
  \<open>sc \<midarrow>r, F /\<rightarrow>\<^sub>e\<^sub>a \<equiv> \<forall>\<gamma>. \<forall>sc'::_\<times>_. \<not> estep aopstep r F \<gamma> sc sc'\<close>

\<comment> \<open> TODO: remove \<close>
subsection \<open> Lemmas about estep \<close>

lemma estep_simps[simp]:
  \<open>estep step R F Env sc sc' =
    (snd sc' = snd sc \<and>
      fst (fst sc') = fst (fst sc) \<and>
      R (snd (fst sc)) (snd (fst sc')) \<and>
      (\<exists>f. F (f, snd (fst sc)) \<and> fst (fst sc) ## f) \<and>
      (\<exists>f. F (f, snd (fst sc')) \<and> fst (fst sc) ## f))\<close>
  \<open>estep step R F (Loc \<alpha>) sc sc' =
    (\<exists>f.
      F (f, snd (fst sc)) \<and>
      fst (fst sc) ## f \<and>
      F (f, snd (fst sc')) \<and>
      fst (fst sc') ## f \<and>
      step \<alpha>
        ((fst (fst sc) + f, snd (fst sc)), snd sc)
        ((fst (fst sc') + f, snd (fst sc')), snd sc'))\<close>
  by (force simp add: estep_def split: sum.splits unit.splits prod.splits)+

lemma estepE[elim]:
  \<open>estep step R F \<alpha>e sc sc' \<Longrightarrow>
    (\<And>xl xs c xs' xf xf'.
      \<alpha>e = Env \<Longrightarrow>
      sc = ((xl, xs), c) \<Longrightarrow>
      sc' = ((xl, xs'), c) \<Longrightarrow>
      R xs xs' \<Longrightarrow>
      F (xf, xs) \<Longrightarrow>
      xl ## xf \<Longrightarrow>
      F (xf', xs') \<Longrightarrow>
      xl ## xf' \<Longrightarrow>
      P) \<Longrightarrow>
    (\<And>\<alpha> xl xs c mx' c' xf mxf'.
      \<alpha>e = Loc \<alpha> \<Longrightarrow>
      sc = ((xl,xs),c) \<Longrightarrow>
      sc' = (mx',c') \<Longrightarrow>
      F (xf, xs) \<Longrightarrow>
      xl ## xf \<Longrightarrow>
      step \<alpha> ((xl + xf,xs),c) (mxf', c') \<and>
      (\<exists>xl' xlf' xs'.
        mxf' = (xlf', xs') \<and>
        F (xf, xs') \<and>
        xl' ## xf \<and>
        xlf' = xl' + xf \<and>
        mx' = (xl', xs')) \<Longrightarrow>
      P) \<Longrightarrow>
    P\<close>
  by (cases sc, cases sc', cases \<alpha>e; force)

lemma estep_def':
  \<open>estep step R F \<alpha>e sc sc' \<longleftrightarrow>
    \<alpha>e = Env \<and>
    (snd sc' = snd sc \<and>
      fst (fst sc') = fst (fst sc) \<and>
      R (snd (fst sc)) (snd (fst sc')) \<and>
      (\<exists>f. F (f, snd (fst sc)) \<and> fst (fst sc) ## f) \<and>
      (\<exists>f. F (f, snd (fst sc')) \<and> fst (fst sc) ## f)) \<or>
    (\<exists>\<alpha>. \<alpha>e = Loc \<alpha> \<and> (\<exists>f.
      F (f, snd (fst sc)) \<and>
      fst (fst sc) ## f \<and>
      F (f, snd (fst sc')) \<and>
      fst (fst sc') ## f \<and>
      step \<alpha>
        ((fst (fst sc) + f, snd (fst sc)), snd sc)
        ((fst (fst sc') + f, snd (fst sc')), snd sc')))\<close>
  by (cases \<alpha>e; simp)

lemma estep_skip_iff[simp]:
  \<open>\<forall>\<alpha> s sc'. \<not> step \<alpha> (s, Skip) sc' \<Longrightarrow>
    estep step R F \<alpha>e (s, Skip) sc' \<longleftrightarrow>
      \<alpha>e = Env \<and>
      snd sc' = Skip \<and>
      fst (fst sc') = fst s \<and>
      R (snd s) (snd (fst sc')) \<and>
      (\<exists>f. F (f, snd s) \<and> fst s ## f) \<and>
      (\<exists>f. F (f, snd (fst sc')) \<and> fst (fst sc') ## f)\<close>
  unfolding estep_def
  by (cases \<alpha>e; clarsimp split: prod.splits)


subsubsection \<open> Eastep Complex Lemmas \<close>

lemma eastep_then_eastep_right_par:
  \<open>(s, c) \<midarrow>R, F, \<pi>\<alpha>e\<rightarrow>\<^sub>e\<^sub>a (s', c') \<Longrightarrow>
    (s, c \<parallel> cb) \<midarrow>R, F, map_eact (apfst PL) \<pi>\<alpha>e\<rightarrow>\<^sub>e\<^sub>a (s', c' \<parallel> cb)\<close>
  unfolding estep_def
  by (force split: prod.splits eact.splits)

lemma eastep_then_eastep_left_par:
  \<open>(s, c) \<midarrow>R, F, \<pi>\<alpha>e\<rightarrow>\<^sub>e\<^sub>a (s', c') \<Longrightarrow>
    (s, ca \<parallel> c) \<midarrow>R, F, map_eact (apfst PR) \<pi>\<alpha>e\<rightarrow>\<^sub>e\<^sub>a (s', ca \<parallel> c')\<close>
  unfolding estep_def
  by (force split: prod.splits eact.splits)

lemma eastep_then_eastep_right_endet:
  \<open>(s, c) \<midarrow>R, F, \<pi>\<alpha>e\<rightarrow>\<^sub>e\<^sub>a (s', c') \<Longrightarrow>
    (\<forall>\<pi>\<alpha>. \<pi>\<alpha>e = Env \<longrightarrow> (s, c \<^bold>\<box> cb) \<midarrow>R, F, \<pi>\<alpha>e\<rightarrow>\<^sub>e\<^sub>a (s', c' \<^bold>\<box> cb)) \<and>
    (\<forall>\<pi>\<alpha>. \<pi>\<alpha>e = Loc \<pi>\<alpha> \<longrightarrow>
      (vis_aact (snd \<pi>\<alpha>) \<longrightarrow> (s, c \<^bold>\<box> cb) \<midarrow>R, F, \<pi>\<alpha>e\<rightarrow>\<^sub>e\<^sub>a (s', c')) \<and>
      (tau_aact (snd \<pi>\<alpha>) \<longrightarrow> (s, c \<^bold>\<box> cb) \<midarrow>R, F, \<pi>\<alpha>e\<rightarrow>\<^sub>e\<^sub>a (s', c' \<^bold>\<box> cb)))\<close>
  unfolding estep_def
  by (force split: prod.splits simp add: vis_aact_def tau_aact_def)

lemma eastep_then_eastep_left_endet:
  \<open>(s, c) \<midarrow>R, F, \<pi>\<alpha>e\<rightarrow>\<^sub>e\<^sub>a (s', c') \<Longrightarrow>
    (\<forall>\<pi>\<alpha>. \<pi>\<alpha>e = Env \<longrightarrow> (s, ca \<^bold>\<box> c) \<midarrow>R, F, \<pi>\<alpha>e\<rightarrow>\<^sub>e\<^sub>a (s', ca \<^bold>\<box> c')) \<and>
    (\<forall>\<pi>\<alpha>. \<pi>\<alpha>e = Loc \<pi>\<alpha> \<longrightarrow>
      (vis_aact (snd \<pi>\<alpha>) \<longrightarrow> (s, ca \<^bold>\<box> c) \<midarrow>R, F, \<pi>\<alpha>e\<rightarrow>\<^sub>e\<^sub>a (s', c')) \<and>
      (tau_aact (snd \<pi>\<alpha>) \<longrightarrow> (s, ca \<^bold>\<box> c) \<midarrow>R, F, \<pi>\<alpha>e\<rightarrow>\<^sub>e\<^sub>a (s', ca \<^bold>\<box> c')))\<close>
  unfolding estep_def
  by (force split: prod.splits simp add: vis_aact_def tau_aact_def)

lemma estep_then_estep_doloop:
  \<open>(s, c) \<midarrow>R, F, \<pi>\<alpha>e\<rightarrow>\<^sub>e\<^sub>a (s', c') \<Longrightarrow>
    (\<forall>\<pi>\<alpha>. \<pi>\<alpha>e = Env \<longrightarrow> (s, DO c OD) \<midarrow>R, F, \<pi>\<alpha>e\<rightarrow>\<^sub>e\<^sub>a (s', DO c' OD)) \<and>
    (\<forall>\<pi>\<alpha>. \<pi>\<alpha>e = Loc \<pi>\<alpha> \<longrightarrow> (s, DO c OD) \<midarrow>R, F, \<pi>\<alpha>e\<rightarrow>\<^sub>e\<^sub>a (s', c' ;; DO c OD))\<close>
  unfolding estep_def
  by (force split: prod.splits)


lemma aopstep_preserves_reflclC:
  \<open>sscc \<midarrow>\<rho>\<rightarrow>\<^sub>a msscc' \<Longrightarrow>
    reflclC (snd sscc) \<Longrightarrow>
    reflclC (snd msscc')\<close>
  by (induct rule: aopstep_induct)
    (fastforce simp add: if_bool_eq_disj)+

lemma eaopstep_preserves_reflclC:
  \<open>sscc \<midarrow>RR, FF, \<rho>\<rightarrow>\<^sub>e\<^sub>a msscc' \<Longrightarrow>
    reflclC (snd sscc) \<Longrightarrow>
    reflclC (snd msscc')\<close>
  apply (erule estepE)
   apply force
  apply (metis aopstep_preserves_reflclC snd_conv)
  done


subsection \<open> Extended steps \<close>

inductive esteps :: \<open>_ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> bool\<close> for step where
  esteps_nil[intro!]:
  \<open>sc' = sc \<Longrightarrow> esteps step r F [] sc sc'\<close>
| esteps_step[intro!]:
  \<open>estep step r F \<alpha> sc sc' \<Longrightarrow>
    esteps step r F \<rho> sc' sc'' \<Longrightarrow>
    esteps step r F (\<alpha> # \<rho>) sc sc''\<close>

inductive_cases esteps_nilE[elim!]: \<open>esteps step r F [] sc sc'\<close>
inductive_cases esteps_consE[elim!]: \<open>esteps step r F (\<alpha> # \<rho>) sc sc'\<close>

abbreviation esteps_pretty :: \<open>_ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> bool\<close>
  (\<open>_ \<midarrow>_, _, _\<rightarrow>\<^sub>e\<^sup>* _\<close> [55, 0, 0, 0, 55])
  where
    \<open>sc \<midarrow>r, F, \<gamma>s\<rightarrow>\<^sub>e\<^sup>* sc' \<equiv> esteps opstep r F \<gamma>s sc sc'\<close>

lemmas esteps_induct = esteps.induct[of opstep, consumes 1]

abbreviation easteps_pretty :: \<open>_ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> bool\<close>
  (\<open>_ \<midarrow>_, _, _\<rightarrow>\<^sub>e\<^sub>a\<^sup>* _\<close> [55, 0, 0, 0, 55])
  where
    \<open>sc \<midarrow>r, F, \<gamma>s\<rightarrow>\<^sub>e\<^sub>a\<^sup>* sc' \<equiv> esteps aopstep r F \<gamma>s sc sc'\<close>

lemmas easteps_induct = esteps.induct[of aopstep, consumes 1]

lemma easteps_iff[simp]:
  \<open>esteps step R F [] sc sc' \<longleftrightarrow> sc' = sc\<close>
  \<open>esteps step R F (\<alpha> # \<rho>) sc sc'' \<longleftrightarrow>
    (\<exists>sc'. estep step R F \<alpha> sc sc' \<and> esteps step R F \<rho> sc' sc'')\<close>
   by force+


subsection \<open> Reverse Extended Steps \<close>

inductive esteps_rev :: \<open>_ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> bool\<close> for step r F where
  esteps_rev_nil[intro!]:
  \<open>sc' = sc \<Longrightarrow> esteps_rev step r F [] sc sc'\<close>
| esteps_rev_rcons[intro!]: \<open>
  esteps_rev step r F \<rho> sc sc' \<Longrightarrow>
  estep step r F \<alpha> sc' sc'' \<Longrightarrow>
  esteps_rev step r F (\<rho> @ [\<alpha>]) sc sc''\<close>

inductive_cases esteps_rev_nilE[elim!]: \<open>esteps_rev step r F [] sc sc'\<close>
inductive_cases esteps_rev_consE[elim]: \<open>esteps_rev step r F (\<rho> @ [\<alpha>]) sc sc'\<close>

lemmas esteps_rev_singleton[intro!] =
  esteps_rev_rcons[of _ _ _ \<open>[]\<close>, OF esteps_rev_nil, simplified]


abbreviation esteps_rev_pretty :: \<open>_ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> bool\<close>
  (\<open>_ \<midarrow>_, _, _\<rightarrow>\<^sub>e\<^sub>r\<^sup>* _\<close> [55, 0, 0, 0, 55])
  where
    \<open>sc \<midarrow>R, F, \<rho>\<rightarrow>\<^sub>e\<^sub>r\<^sup>* sc' \<equiv> esteps_rev opstep R F \<rho> sc sc'\<close>

lemmas esteps_rev_induct = esteps_rev.induct[of opstep, consumes 1, case_names Nil Rcons]

abbreviation easteps_rev_pretty :: \<open>_ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> bool\<close>
  (\<open>_ \<midarrow>_, _, _\<rightarrow>\<^sub>e\<^sub>a\<^sub>r\<^sup>* _\<close> [55, 0, 0, 0, 55])
  where
    \<open>sc \<midarrow>R, F, \<rho>\<rightarrow>\<^sub>e\<^sub>a\<^sub>r\<^sup>* sc' \<equiv> esteps_rev aopstep R F \<rho> sc sc'\<close>

lemmas easteps_rev_induct = esteps_rev.induct[of aopstep, consumes 1, case_names Nil Rcons]

lemma easteps_rev_iff[simp]:
  \<open>esteps_rev step R F [] sc sc' \<longleftrightarrow> sc' = sc\<close>
  \<open>esteps_rev step R F (\<rho> @ [\<alpha>]) sc sc'' \<longleftrightarrow>
    (\<exists>sc'. esteps_rev step R F \<rho> sc sc' \<and> estep step R F \<alpha> sc' sc'')\<close>
  by force+

paragraph \<open> Esteps-rev to Esteps \<close>

lemma esteps_rev_esteps_to_esteps:
  \<open>esteps_rev step R F \<rho>x sc sc' \<Longrightarrow>
    esteps step R F \<rho>y sc' sc'' \<Longrightarrow>
    esteps step R F (\<rho>x @ \<rho>y) sc sc''\<close>
  by (induct arbitrary: \<rho>y sc'' rule: esteps_rev.induct) force+

lemma esteps_rev_to_esteps:
  \<open>esteps_rev step R F \<rho> sc sc' \<Longrightarrow> esteps step R F \<rho> sc sc'\<close>
  using esteps_rev_esteps_to_esteps[where \<rho>y=\<open>[]\<close> and sc'=sc' and sc''=sc', of step R F]
  by (case_tac sc', simp)

paragraph \<open> Esteps to Esteps-rev \<close>

lemma esteps_rev_esteps_to_esteps_rev:
  \<open>esteps step R F \<rho>y sc' sc'' \<Longrightarrow>
    esteps_rev step R F \<rho>x sc sc' \<Longrightarrow>
    esteps_rev step R F (\<rho>x @ \<rho>y) sc sc''\<close>
  by (induct arbitrary: \<rho>x rule: esteps.induct) force+

lemma esteps_to_esteps_rev:
  \<open>esteps step R F \<rho> sc sc' \<Longrightarrow> esteps_rev step R F \<rho> sc sc'\<close>
  using esteps_rev_esteps_to_esteps_rev[where \<rho>x=\<open>[]\<close> and sc=sc and sc''=sc', of step R F, simplified]
  by auto


section \<open> Security \<close>

subsection \<open> parallel-annotated opsteps \<close>

inductive aopsteps
  :: \<open>_ list \<Rightarrow>
      ('l \<times> 's) \<times> ('l \<times> 's) comm \<Rightarrow>
      ('l \<times> 's) \<times> ('l \<times> 's) comm \<Rightarrow>
      bool\<close>
  where
  aopsteps_nil[intro!]:
  \<open>sc' = sc \<Longrightarrow> aopsteps [] sc sc'\<close>
| aopsteps_step[intro]:
  \<open>aopstep \<alpha> sc sc' \<Longrightarrow>
    aopsteps \<rho> sc' sc'' \<Longrightarrow>
    aopsteps (\<alpha> # \<rho>) sc sc''\<close>

inductive_cases aopsteps_nilE[elim!]: \<open>aopsteps [] sc sc'\<close>
inductive_cases aopsteps_consE[elim]: \<open>aopsteps (\<alpha> # \<rho>) sc sc'\<close>

lemmas aopsteps_induct = aopsteps.induct[case_names nil crash step]

abbreviation aopsteps_pretty :: \<open>_ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> bool\<close> (\<open>_ \<midarrow>_\<rightarrow>\<^sub>a\<^sup>* _\<close> [50, 0, 50]) where
  \<open>sc \<midarrow>\<rho>a\<rightarrow>\<^sub>a\<^sup>* sc' \<equiv> aopsteps \<rho>a sc sc'\<close>

lemma aopsteps_simps[simp]:
  \<open>aopsteps [] sc sc' \<longleftrightarrow> sc' = sc\<close>
  \<open>aopsteps (\<alpha> # \<rho>) sc sc'' \<longleftrightarrow> (\<exists>sc'. aopstep \<alpha> sc sc' \<and> aopsteps \<rho> sc' sc'')\<close>
  by blast+

subsubsection \<open> Lemmas \<close>

lemma aopsteps_tau_preserves_state:
  \<open>sc \<midarrow>\<rho>\<rightarrow>\<^sub>a\<^sup>* sc' \<Longrightarrow> list_all (tau_aact \<circ> snd) \<rho> \<Longrightarrow> fst sc' = fst sc\<close>
  by (induct rule: aopsteps.induct)
    (fastforce split: if_splits simp add: tau_aact_def dest: aopstep_tau_preserves_state)+

lemma aopsteps_rcons:
  \<open>sc \<midarrow>\<rho>\<rightarrow>\<^sub>a\<^sup>* sc' \<Longrightarrow>
    sc' \<midarrow>\<pi>\<alpha>\<rightarrow>\<^sub>a sc'' \<Longrightarrow>
    sc \<midarrow>\<rho> @ [\<pi>\<alpha>]\<rightarrow>\<^sub>a\<^sup>* sc''\<close>
  by (induct arbitrary: sc'' rule: aopsteps.induct)
   fastforce+

lemma aopsteps_iff:
  \<open>sc \<midarrow>\<rho>\<rightarrow>\<^sub>a\<^sup>* sc'' \<longleftrightarrow>
    \<rho> = [] \<and> sc'' = sc \<or>
    (\<exists>\<pi>\<alpha> \<rho>'. \<rho> = \<pi>\<alpha> # \<rho>' \<and> (\<exists>sc'. sc \<midarrow>\<pi>\<alpha>\<rightarrow>\<^sub>a sc' \<and> sc' \<midarrow>\<rho>'\<rightarrow>\<^sub>a\<^sup>* sc''))\<close>
  by (induct \<rho>) force+

lemma aopsteps_Skip_iif[simp]:
  \<open>(s, Skip) \<midarrow>\<rho>\<rightarrow>\<^sub>a\<^sup>* sc'' \<longleftrightarrow> sc'' = (s, Skip) \<and> \<rho> = []\<close>
  by (cases sc'', induct \<rho>; force)

lemma baopsteps_tau_preserves_state:
  \<open>sc \<midarrow>\<rho>\<rightarrow>\<^sub>a\<^sup>* sc' \<Longrightarrow>
    list_all ((=) TauBasic \<circ> snd) \<rho> \<Longrightarrow>
    fst sc' = fst sc\<close>
  by (simp add: aopsteps_tau_preserves_state list.pred_set)

lemma btau_aexec_preserves_nextstep:
  \<open>sc \<midarrow>\<rho>\<rightarrow>\<^sub>a\<^sup>* sc' \<Longrightarrow>
    list_all ((=) TauBasic \<circ> snd) \<rho> \<Longrightarrow>
    list_all ((\<noteq>) \<pi>\<alpha>x) \<rho> \<Longrightarrow>
    sc \<midarrow>\<pi>\<alpha>x\<rightarrow>\<^sub>a scx \<Longrightarrow>
    \<exists>cx'. sc' \<midarrow>\<pi>\<alpha>x\<rightarrow>\<^sub>a (fst scx, cx')\<close>
  apply (induct arbitrary: \<pi>\<alpha>x scx rule: aopsteps_induct)
   apply force
  apply (simp, elim conjE)
  apply (frule(3) btau_astep_preserves_nextstep)
  apply (clarsimp, blast)
  done

lemma aopsteps_trans:
  \<open>sc \<midarrow>\<rho>a\<rightarrow>\<^sub>a\<^sup>* sc' \<Longrightarrow>
    sc' \<midarrow>\<rho>b\<rightarrow>\<^sub>a\<^sup>* sc'' \<Longrightarrow>
    sc \<midarrow>\<rho>a @ \<rho>b\<rightarrow>\<^sub>a\<^sup>* sc''\<close>
  by (induct arbitrary: \<rho>b sc'' rule: aopsteps.induct) force+


end
