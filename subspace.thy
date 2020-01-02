theory subspace imports topological_space   begin

definition (in topological_space)
  subspace_topology :: "'a set \<Rightarrow>'a set set" where
(* "subspace_topology  S  \<equiv>   { \<forall>t \<in> T. S \<inter> t }  "*)
  "subspace_topology  S = {a .\<exists>u\<in>T. a = S \<inter> u }"
thm topological_space.subspace_topology_def



lemma  (in topological_space) subspace_inter[simp ,intro]:
  assumes    a1 : "S \<subseteq> X"
  and        a2 : "x \<in> {a. \<exists>u\<in>T. a = S \<inter> u}"
  and        a3 : "y \<in> {a. \<exists>u\<in>T. a = S \<inter> u}"
  shows   "x \<inter> y \<in> {a. \<exists>u\<in>T. a = S \<inter> u}"
 
proof-
  from a2  have b : "\<exists>u1\<in>T. x = S \<inter> u1   "  apply simp done
  from a3 have c : "\<exists>u2\<in>T. y = S \<inter> u2   "  apply simp done
  from b c have d : "\<exists>u1\<in>T. \<exists>u2\<in> T. x \<inter> y = S \<inter> (u1 \<inter> u2)" apply blast  done
  from  d have e : "\<exists>u1\<in>T. \<exists>u2\<in> T. x \<inter> y = S \<inter> (u1 \<inter> u2) \<and> (u1 \<inter> u2 \<in> T)"  
            apply  (simp add:topological_space_def) done
 from e have  f : "\<exists>u3\<in>T. x \<inter> y = S \<inter> u3  "  apply blast done 
 from a1 a2 a3  f  show ?thesis apply blast  done
qed


definition (in topological_space) map_B :: "['a set , 'a set  ]\<Rightarrow> 'a set " where
   " map_B S a  = \<Union>{u.  a = S \<inter>  u \<and> u \<in> T}"

lemma (in topological_space) subspace_in_T[simp,intro]:
 "{u. a=S \<inter> u \<and> u \<in> T} \<subseteq> T "
apply blast
done

lemma (in topological_space)subspace_union[simp,intro]:
  assumes  a1:  "S \<subseteq> X"
  and      a2:  " A \<subseteq> {a. \<exists>u\<in>T. a = S \<inter> u}"
(*  and      a3:  "\<And>a. \<lbrakk>a\<in>A\<rbrakk>  \<Longrightarrow> B a \<in> T  "
  and      a4:  "\<And>a. \<lbrakk>a\<in>A\<rbrakk>  \<Longrightarrow> ( a = (S \<inter> (B a)))"*)
  shows    "\<exists>u\<in>T. \<Union>A = S \<inter> u"
proof-
  from  a2  have s1:  "\<Union>A = \<Union>{a. a\<in>A}"  apply (simp) done
  from  a2   have s2 : "\<Union>{a. a\<in>A}= \<Union>{c. \<exists>a\<in>A. c =a }" apply (simp) done
  from  a1 a2  have s3: "\<And>a. \<lbrakk> a\<in>A \<rbrakk> \<Longrightarrow>  (map_B S a ) \<in> T" 
             apply(simp add:map_B_def subspace_in_T)   done  
             (*apply blast  done*)
 from a2 s3 have s4: "\<And>a. \<lbrakk>a\<in>A\<rbrakk>  \<Longrightarrow> ( a = (S \<inter> (map_B S a)))" apply (simp add:map_B_def) apply blast done
  from  s4   have s5 : "{c. \<exists>a\<in>A. c=a}={c. \<exists>a\<in>A. c= S \<inter> map_B S a }  " apply  simp  done  
  from s1 s2 s5 have s6 : "\<Union>A = \<Union>{c. \<exists>a\<in>A. c=S \<inter> map_B S  a } "  apply simp done
  from s3 s4 have s7  : "\<Union>{c. \<exists>a\<in>A. c= S \<inter> (map_B S a)} = \<Union>{u. \<exists>a\<in>A. u =(map_B S  a) } \<inter> S " apply blast done
  from a2 s3 s4  have  s8: "\<And>t. \<lbrakk>t\<in>{u. \<exists>a\<in>A. u =map_B S a}\<rbrakk> \<Longrightarrow> t \<in>  T" 
        apply (simp add :Pi_def) apply blast done
  from s8 have  s9 : "{u. \<exists>a\<in>A. u =map_B S a} \<subseteq> T " apply blast done
  from s9 have  s10 : "\<Union>{u. \<exists>a\<in>A. u =map_B S a} \<in> T " 
         apply(simp add:map_B_def subspace_in_T) done
  from s10 have s11 : "\<exists>u\<in>T. u=\<Union>{u. \<exists>a\<in>A. u =map_B S a}" apply simp done
  from s1 s2 s6 s7 have s12: "\<Union>A = \<Union>{u. \<exists>a\<in>A. u =map_B S a } \<inter> S " apply simp done
  from s11 s12 have s13 : "\<exists>u\<in>T. \<Union>A= u \<inter> S"   apply blast done
  have s14 : "\<forall>u\<in>T. u \<inter> S = S \<inter> u" apply blast done
  (*from m n  have o: "\<exists>u\<in>T. \<Union>A = S \<inter> u" apply simp  done*)
  from s13 s14  show  ?thesis apply simp done
qed



  

lemma (in topological_space)subspace_union_1[simp,intro]:
"\<lbrakk> S \<subseteq> X ; A \<subseteq> {a. \<exists>u\<in>T. a = S \<inter> u}\<rbrakk>  \<Longrightarrow> \<exists>u\<in>T. \<Union>A = S \<inter> u"
apply (blast intro: subspace_union)
done

lemma (in topological_space) empty_in_subspace:
"{} \<in> {a. \<exists>u\<in>T. a = S \<inter> u}"
apply simp
apply auto
done

lemma (in topological_space)S_in_subspace:
" S \<subseteq> X \<Longrightarrow> S \<in> {a. \<exists>u\<in>T. a = S \<inter> u}"
apply auto
done

thm topological_space.subspace_topology_def

lemma (in topological_space) 
   subspace_is_top:
  "\<lbrakk>S \<subseteq> X\<rbrakk> \<Longrightarrow> 
    topological_space S (subspace_topology S)"
apply (simp add:subspace_topology_def)
apply  (rule topological_space.intro)
apply  blast
apply  (rule empty_in_subspace)
apply (rule S_in_subspace,assumption+)
apply (erule subspace_inter,assumption+)
apply (simp add: subspace_union_1)
done

end