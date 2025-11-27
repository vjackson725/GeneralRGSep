theory LangExperimental
  imports SepAlgInstancesExperimental "../Lang"
begin

subsection \<open> Locked shared state \<close>

definition acquire
  :: \<open>nat \<Rightarrow> 'a::perm_alg \<times> 'a resources \<Rightarrow> 'a \<times> 'a resources \<Rightarrow> bool\<close>
  where
  \<open>acquire lk \<equiv> \<lambda>(l,s) (l',s'). (\<exists>st.
      s lk = Some (Unlocked st) \<and>
      l ## st \<and>
      l' = l + st \<and>
      s' = s(lk \<mapsto> Locked)
  )\<close>

end