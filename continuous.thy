theory continuous imports topological_space  subspace  begin


     (*
definition
  is_inj :: "'a set \<Rightarrow> 'b set \<Rightarrow> bool" where
  "is_inj A B \<longleftrightarrow> (inj_on f A) \<and> (f: A \<longrightarrow> B) "

definition
  SUR :: "'a set \<Rightarrow> 'b set \<Rightarrow> ('a \<Rightarrow> 'b) set" where
  "SUR A B = {f. f : A \<rightarrow> B \<and> (\<forall> y\<in>B. \<exists> x\<in>A. y = f x)}"

definition
  BIJ :: "'a set \<Rightarrow> 'b set \<Rightarrow> ('a \<Rightarrow> 'b) set" where
  "BIJ A B = INJ A B \<inter> SUR A B"

definition
  card_le :: "'a set \<Rightarrow> 'b set \<Rightarrow> bool" (infix "cardle" 50) where
  "A cardle B \<longleftrightarrow> (\<exists>f. f \<in> SUR B A)"
*)

definition fun_image :: "['a\<Rightarrow> 'b,'a set , 'b set] \<Rightarrow> 'b set" where
  "fun_image (f::'a\<Rightarrow>'b ) A Y = {b .\<exists>a\<in>A.  b = (f a) \<and> b\<in> Y }"



definition fun_preimage  :: "['a\<Rightarrow> 'b,'b set, 'a set] \<Rightarrow> 'a set" where
  "fun_preimage (f::'a\<Rightarrow>'b ) B  X= {a .(f a \<in> B)\<and> a \<in> X }"


definition 
   continuous :: 
   "['a \<Rightarrow> 'b, 'a set,'a set set,
      'b set ,'b set set  ] \<Rightarrow>bool"
      where 
   "continuous f  X Tx Y Ty == (f: X \<rightarrow> Y) 
       \<and>(topological_space X Tx) 
       \<and> (topological_space Y Ty)
       \<and> (\<forall>V. (topological_space.open_set Ty V )\<longrightarrow>
          ( topological_space.open_set Tx 
              (fun_preimage f V X))  )"



lemma closed_set_continuous_1:
  assumes  a1 : "f:X \<rightarrow> Y"
  and      a2 : "topological_space X Tx"
  and      a3 : "topological_space Y Ty"
  and      a4 : "\<forall>V. topological_space.closed_set Y Ty V \<longrightarrow> topological_space.closed_set X Tx (fun_preimage f V X) "
  and      a5 : "topological_space.open_set Ty A"
  shows   "topological_space.open_set Tx  (fun_preimage f A X)"
proof-
     from a3  a5 have s1 : "A \<in> Ty "  apply (simp add: topological_space.open_set_def)  done
     from a3 s1 have s2  : "Ty \<subseteq>  Pow Y" apply (simp add :topological_space_def) done
     from s1 s2 have s3 : "A \<subseteq> Y"  apply blast done
     from s3 have s4 : "Y - A \<subseteq> Y"  apply blast done
     from s3 s4 have s5: "Y - (Y - A) = A" apply blast done
     from a3 a5 s4 s5 have s6 : "topological_space.closed_set Y Ty  (Y - A)" 
             apply (simp add: topological_space.closed_set_def)  done 
     from a4 s6 have s7: "topological_space.closed_set X Tx  (fun_preimage f (Y-A) X )" 
             apply simp done
     from s7 a2  have s8: "(X - (fun_preimage f (Y-A) X)) \<in> Tx " 
             apply (simp add:topological_space.closed_set_def topological_space.open_set_def)  done
       have s8_1 : " X - {a. f a \<in> Y \<and> f a \<notin> A \<and> a \<in> X} = {a. (f a \<notin> Y \<or> f a \<in> A) \<and> a \<in> X}" apply blast done        
       have s8_2 : "{a. (f a \<notin> Y \<or> f a \<in> A) \<and> a \<in> X} = {a. (f a \<notin> Y) \<and> a \<in> X} \<union> {a. (f a \<in>  Y \<and>  f a \<in>   A) \<and> a \<in> X}" apply blast  done 
       from a1 have s8_3:"\<forall>a\<in>X. f a \<in> Y  "  apply (simp add: Pi_def) done
       from s8_3 have s8_4 : "{a. (f a \<notin> Y) \<and> a \<in> X} = {}"  apply blast done
       from s8_2 s8_4 have s8_5 : "{a. (f a \<notin> Y \<or> f a \<in> A) \<and> a \<in> X} = {a. (f a \<in>  Y \<and>  f a \<in>   A) \<and> a \<in> X}"  apply simp done
       from s8_1 s8_5 have s8_6 : " X - {a. f a \<in> Y \<and> f a \<notin> A \<and> a \<in> X} = {a. (f a \<in>  Y \<and>  f a \<in>   A) \<and> a \<in> X}"  apply  simp done
       have s8_7 : "X - {a. f a \<in> Y \<and> f a \<notin> A \<and> a \<in> X} = X - (fun_preimage f (Y-A) X) "  apply  (simp add: fun_preimage_def) done
       from s3 have s8_8 : "{a. (f a \<in>  Y \<and>  f a \<in>   A) \<and> a \<in> X} = {a. (f a \<in> A) \<and> a \<in> X}" apply blast done
       have s8_9 : "{a. (f a \<in> A) \<and> a \<in> X} = (fun_preimage f A X)" apply (simp add: fun_preimage_def) done 
       from s8_9 s8_8 s8_6 s8_7  have s8_10 : "X - (fun_preimage f (Y-A) X) = (fun_preimage f A X) "  apply simp done
       from s8 s8_10 have s9: " (fun_preimage f A X) \<in> Tx" apply simp done
       from a2 s9 show ?thesis  apply  (simp add:topological_space.open_set_def) done
qed

 

lemma closed_set_continuous_2:
 "\<And>A. \<lbrakk> f:X \<rightarrow> Y;
        topological_space X Tx ;
        topological_space Y Ty;
        \<forall>V. (topological_space.closed_set Y Ty  V) \<longrightarrow> (topological_space.closed_set X Tx (fun_preimage f V X));
         (topological_space.open_set Ty  A)    
      \<rbrakk> \<Longrightarrow> (topological_space.open_set Tx  (fun_preimage f A X)) "
apply (rule closed_set_continuous_1)
apply simp+
done
(*lemma "A \<and> B \<longrightarrow> B \<and> A"
proof
 assume AB:"A \<and> B"
 from AB show "B \<and> A"
*)


lemma closed_set_continuous:
  assumes  a1 : "f:X \<rightarrow> Y"
  and      a2 : "topological_space X Tx"
  and      a3 : "topological_space Y Ty"
  and      a4 : "\<forall>V. topological_space.closed_set Y Ty  V \<longrightarrow> topological_space.closed_set X Tx(fun_preimage f V X) "
  shows   "continuous f X Tx Y Ty"
proof-
  from a1 a2 a3 a4  have s1:"\<And>A. \<lbrakk> (topological_space.open_set Ty A)\<rbrakk> \<Longrightarrow> topological_space.open_set Tx  (fun_preimage f A X)  " apply (rule  closed_set_continuous_1) apply simp+ done
  from s1 have s2 : "\<forall>A. (topological_space.open_set Ty A) \<longrightarrow>  (topological_space.open_set Tx (fun_preimage f A X)) " apply simp done
  from  a1 a2 a3 s2  show ?thesis  apply (simp add:  continuous_def) done
qed

lemma continuous_2_closed_set_1:
  assumes a1 : "continuous f X Tx Y Ty"
  and     a2 : "topological_space.closed_set Y Ty  A "
  shows   "topological_space.closed_set X Tx (fun_preimage f A X)"
proof-
  from a1 have s1: "f:X \<rightarrow> Y" apply (simp add:continuous_def) done
  from a1 have s2: "topological_space X Tx" apply (simp add:continuous_def)  done
  from a1 have s3: "topological_space Y Ty" apply (simp add:continuous_def)  done
  from a1 have s4: "\<forall>V. topological_space.open_set Ty  V \<longrightarrow> topological_space.open_set Tx  (fun_preimage f V X)" 
                    apply(simp add:continuous_def) done
  from s3 a2 have s5 : "topological_space.open_set Ty (Y-A)"  apply (simp add: topological_space.closed_set_def) done
  from s4 s5 have s6 : "topological_space.open_set Tx  (fun_preimage f (Y-A) X)" apply (simp) done
  from s2 s6 have s7 : " (fun_preimage f (Y-A) X) \<subseteq> X"  apply (simp add: fun_preimage_def)  apply blast done
  from s7 have s8 : "(X- (fun_preimage f (Y-A) X)) \<subseteq> X" apply blast done
  from s7 s8 have s9 : "(X - (X - (fun_preimage f (Y - A) X))) = (fun_preimage f (Y - A) X )"  apply blast done
  from s2 s6 s8 s9 have s10 : "topological_space.closed_set X Tx (X- (fun_preimage f (Y-A) X))" apply (simp add:topological_space.closed_set_def) done
   have s11_1 : "X - {a. f a \<in> Y \<and> f a \<notin> A \<and> a \<in> X}={a. (f a \<notin> Y \<or> f a \<in> A ) \<and> a \<in> X} "apply blast done
   have s11_2 : "{a. (f a \<notin> Y \<or> f a \<in> A) \<and> a \<in> X} = {a. (f a \<notin> Y) \<and> a \<in> X} \<union> {a. (f a \<in> A \<and>   f a \<in> Y) \<and> a \<in> X} " 
                     apply blast done
   from s1 have s11_3 : "{a. (f a \<notin> Y) \<and> a \<in> X} ={}"  apply (simp add:Pi_def) apply blast done
   from a2 s3  have s11_4 : "A \<subseteq> Y" apply (simp add:topological_space.closed_set_def)  done
   from s11_4 have s11_5: "{a. (f a \<in> A \<and>   f a \<in> Y) \<and> a \<in> X} = {a. (f a \<in> A ) \<and> a \<in> X}" apply blast  done
   from s11_1 s11_2 s11_3 s11_5  have s11_6 : "{a. f a \<in> A \<and> a \<in> X} = X - {a. f a \<in> Y \<and> f a \<notin> A \<and> a \<in> X}" 
                                                   apply simp done
   have s11: "(fun_preimage f A X) = (X- (fun_preimage f (Y-A) X))"
         apply (simp add:fun_preimage_def s11_6)  done
   from s10 s11 show ?thesis apply simp done
qed
lemma continuous_2_closed_set:
   "\<And>V. \<lbrakk>(continuous f X Tx Y Ty); (topological_space.closed_set Y Ty V)\<rbrakk> \<Longrightarrow>  (topological_space.closed_set X Tx  (fun_preimage f V X))"
apply (simp add:  continuous_2_closed_set_1) 
done     

lemma  pasting_lemma_1:
    assumes       a1: "\<And>x. \<lbrakk>x\<in> A\<rbrakk> \<Longrightarrow>  h x = f x "
    shows    "{a. h a \<in> C \<and> a \<in> A} ={a. f a \<in> C \<and> a \<in> A}" 
proof-
       have t1: "\<And>x.  \<lbrakk>x\<in> {a. h a \<in> C \<and> a \<in> A}\<rbrakk>\<Longrightarrow>  x\<in> A \<and> h x \<in> C"  apply simp done
       from  a1  have  t2:"\<And>x.  \<lbrakk> x\<in> A; h x \<in> C\<rbrakk> \<Longrightarrow> h x  = f x " apply simp  done  
       from t2 have t3 : "\<And>x.  \<lbrakk> x\<in> A; h x \<in> C\<rbrakk> \<Longrightarrow> f x \<in> C \<and> x \<in> A" apply simp  done
       from t3  have t4 : "\<And>x.  \<lbrakk>x\<in> {a. h a \<in> C \<and> a \<in> A}\<rbrakk>\<Longrightarrow> f x \<in> C \<and> x \<in> A" apply simp done 
       have t5: " \<lbrakk>x\<in> A ; f x \<in> C \<rbrakk> \<Longrightarrow>x \<in> {a. f a \<in> C \<and> a\<in> A} " apply simp done 
       from t4 t5 have t6: "\<And>x.  \<lbrakk>x\<in> {a. h a \<in> C \<and> a \<in> A}\<rbrakk>\<Longrightarrow>x \<in> {a. f a \<in> C \<and> a\<in> A}" apply blast  done
       from t6 have t7: "{a. h a \<in> C \<and> a \<in> A} \<subseteq> {a. f a \<in> C \<and> a\<in> A} " apply blast done
       have t8:"\<And>x.  \<lbrakk>x\<in> {a. f a \<in> C \<and> a \<in> A}\<rbrakk>\<Longrightarrow>  x\<in> A \<and> f x \<in> C"  apply simp done
       from  a1  have  t9:"\<And>x.  \<lbrakk> x\<in> A; f x \<in> C\<rbrakk> \<Longrightarrow> h x  = f x " apply simp  done 
       from t9  have t10 : "\<And>x.  \<lbrakk> x\<in> A; f x \<in> C\<rbrakk> \<Longrightarrow> h x \<in> C \<and> x \<in> A" apply simp  done
       from t10  have t11 : "\<And>x.  \<lbrakk>x\<in> {a. f a \<in> C \<and> a \<in> A}\<rbrakk>\<Longrightarrow> h x \<in> C \<and> x \<in> A" apply simp done 
       have t12: " \<lbrakk>x\<in> A ; h x \<in> C \<rbrakk> \<Longrightarrow>x \<in> {a. h a \<in> C \<and> a\<in> A} " apply simp done 
       from t11 t12 have t13: "\<And>x.  \<lbrakk>x\<in> {a. f a \<in> C \<and> a \<in> A}\<rbrakk>\<Longrightarrow>x \<in> {a. h a \<in> C \<and> a\<in> A}" apply blast  done
       from t13 have t14: "{a. f a \<in> C \<and> a \<in> A} \<subseteq> {a. h a \<in> C \<and> a\<in> A} " apply blast done 
       from t7 t14  show ?thesis apply simp done
qed

thm topological_space.subspace_topology_def

lemma sub_open : 
  assumes  a1: "topological_space  X T"
  and      a2: "A \<subseteq> X"
  and      a3: "topological_space.open_set T A"
  and      a4: "topological_space.open_set (topological_space.subspace_topology T A)  B"
  shows    "topological_space.open_set T  B"
proof-
   from a1 a2    have s1: "topological_space A (topological_space.subspace_topology T A)" 
        apply (rule topological_space.subspace_is_top) done 
   from  a4 s1  have s2:"B \<in> (topological_space.subspace_topology T A) " 
        apply (simp add: topological_space.open_set_def ) done
   from a1 a3 have s3 : "A \<in> T" 
        apply (simp add:topological_space.open_set_def) done 
   from  a1 a2 a3 a4 s1 s2 have s4: "\<exists>u\<in>T. B = u \<inter>  A  "   
        apply  (simp add:topological_space.open_set_def 
                         topological_space.subspace_topology_def)  
        apply blast  done
   from a1 s3 s4 have s5: "\<And>u.  \<lbrakk> u\<in> T; B = u \<inter>  A \<rbrakk> \<Longrightarrow>  B \<in> T   " 
        apply (simp add: topological_space.O4) done
   from s5 s4  have s6: "B \<in> T"  apply simp apply blast done 
   from a1 s6  show  ?thesis  
        apply (simp add:topological_space.open_set_def) done
qed

lemma union_eq:
 "\<lbrakk> A = B \<rbrakk> \<Longrightarrow> A \<union> C = B \<union> C"
apply blast 
done

lemma sub_closed:
  assumes a1:  "topological_space X T"
  and     a2:  "A \<subseteq> X"
  and     a3:  "topological_space.closed_set X T A"
  and     a4:  "topological_space.closed_set A (topological_space.subspace_topology T A) B"
  shows    "topological_space.closed_set X T B"
proof-
 from a1 a2 have s1: "topological_space A (topological_space.subspace_topology T A)" 
      apply (rule topological_space.subspace_is_top) done 
 from  a4  s1  have s2:" A - B \<in>  (topological_space.subspace_topology T A) " 
      apply (simp add:topological_space.closed_set_def 
                      topological_space.open_set_def ) done
 from a1 a3 have s3: " X-A \<in> T"  
      apply (simp add:topological_space.closed_set_def 
                      topological_space.open_set_def)  done
 from a1 a2 a3 a4 s1 s2 have s4: "\<exists>u\<in>T.  A - B = ( A \<inter> u)  "   
      apply  (simp add:topological_space.closed_set_def 
                       topological_space.open_set_def 
                       topological_space.subspace_topology_def)  done
 from a2 have s5: "(A - B) = A \<inter> (X - B)" apply blast done
 from a2 s5 have s6: "(A \<inter> (X - B)) \<union> (X - A) = (X -B) \<union> (X - A) "  apply blast done
 from a1  a2 a3 a4 s1 have s7: "B \<subseteq> A" 
      apply (simp add:topological_space.closed_set_def) done
 from a2 s7  have s8: "(X - B) \<union> (X - A) = X - B "  apply blast done
 from s5 s6 s7 s8 have s9 : "(A - B)\<union> (X - A) = X -B  " apply blast done
 from a2 have s10 : "\<And> u.  (A \<inter> u)\<union> (X - A) =  X\<inter>   (u \<union> (X - A))"  apply blast done
 from s4 have s11 : "\<And>u.  \<lbrakk> A - B = A \<inter> u\<rbrakk> \<Longrightarrow> (A - B) \<union> (X -A) = (A \<inter> u) \<union> (X -A) "  apply simp done
 from s9 s11 have s12: "\<And>u. \<lbrakk> A - B = A \<inter> u\<rbrakk> \<Longrightarrow> X - B = (A \<inter> u) \<union> (X - A) " apply simp done
 from s12 s10 have s13: "\<And>u. \<lbrakk> A - B = A \<inter> u\<rbrakk> \<Longrightarrow> X - B = X \<inter> (u \<union> (X -A)) "  apply simp done
 from  a1 s3 have s14 : "\<And>u. \<lbrakk> u\<in> T\<rbrakk> \<Longrightarrow>X \<inter>  (u \<union> (X - A))\<in> T "  
      apply (simp add: topological_space.O3 
                       topological_space.O4
                       topological_space.union_in_T )
     done  
 from s13 s14 have s15: "\<And>u. \<lbrakk> u\<in>T; A - B = A \<inter> u  \<rbrakk> \<Longrightarrow> X - B \<in> T "  apply simp done
 from s15 s4 have s16 : "X - B \<in> T" apply blast  done
 from a1 s16 a2 s7 show ?thesis 
    apply (simp add:topological_space.closed_set_def 
                    topological_space.open_set_def) done
qed
 
lemma pasting_lemma_2[simp]:
  assumes    a1:  "topological_space X Tx"
  and        a2:  "topological_space Y Ty"
  and        a3:  "X = A \<union>  B"
  and        a4:  "topological_space.open_set Tx  A" 
  and        a5:  "topological_space.open_set Tx  B"
  and        a6:  "f: A \<rightarrow> Y"
  and        a7:  "g: B \<rightarrow> Y"
  and        a8:  "continuous f A (topological_space.subspace_topology Tx  A)  Y Ty"
  and        a9:  "continuous g B (topological_space.subspace_topology Tx  B)  Y Ty"
  and        a10:  "\<And>x. \<lbrakk>x\<in> A \<inter> B\<rbrakk> \<Longrightarrow> f x = g x "
  and        a11: "\<And>x. \<lbrakk>x\<in> A\<rbrakk> \<Longrightarrow>  h x = f x "
  and        a12: "\<And>x. \<lbrakk>x\<in> B\<rbrakk> \<Longrightarrow> h x = g x "
  and        a13: "topological_space.open_set Ty C"
  shows      "topological_space.open_set Tx (fun_preimage h C X)"
proof-
    from a3 a6 a7 a10 a11 a12 have s1: "h \<in> X \<rightarrow>Y"  apply( simp add :Pi_def)  done
    from  a11    have s2: "{a. h a \<in> C \<and> a \<in> A} ={a. f  a \<in> C \<and> a \<in> A}"  
       apply (rule  pasting_lemma_1) apply blast done
    from a12    have s3: "{a. h a \<in> C \<and> a \<in> B} ={a. g  a \<in> C \<and> a \<in> B}"  
       apply (rule  pasting_lemma_1) apply blast done
    from  a3 a13 have s4 : "{a . h a \<in> C \<and> a \<in> X } = {a. h a \<in> C \<and>  a \<in> A} \<union> {a. h a \<in> C \<and> a \<in> B} " 
       apply blast done
    from  s2 s3 s4 have s5 :"{a . h a \<in> C \<and> a \<in> X } ={a. f  a \<in> C \<and> a \<in> A} \<union> {a. g  a \<in> C \<and> a \<in> B}"  
       apply simp done
    from  s4 s5 have   s6:  "fun_preimage h C X = (fun_preimage f C A) \<union> (fun_preimage g C B)" apply (simp add:fun_preimage_def) done
    from a3 have s7:"A \<subseteq> X" apply blast done
    from a1 a3 s7  have s8: "topological_space A (topological_space.subspace_topology Tx A)"  
        apply  (simp add:topological_space.subspace_is_top) done
    from a1 a4 a13 a8  s8 have s9:
         "topological_space.open_set (topological_space.subspace_topology Tx A) (fun_preimage f C A)"  
         apply (simp add:continuous_def) done
    from  a1  a4  s7 s9 have s10: "topological_space.open_set Tx (fun_preimage f C A)"
         apply (simp add: sub_open)  done
    from a3 have s11:"B \<subseteq> X" apply blast done
    from a1 a3 s11  have s12: 
           "topological_space B (topological_space.subspace_topology Tx B)"  
         apply  (simp add:topological_space.subspace_is_top) done
    from a1 a5 a13 a9  s12 have s13: 
            "topological_space.open_set 
                (topological_space.subspace_topology Tx B) 
                (fun_preimage g C B)" 
           apply (simp add:continuous_def) done
    from  a1  a5 s11 s13 have s14:
             "topological_space.open_set Tx (fun_preimage g C B)"
           apply (simp add: sub_open) done
    from  a1 s10   have s15: "(fun_preimage f C A) \<in> Tx "  
           apply (simp add: topological_space.open_set_def)   done
    from  a1 s14   have s16: "(fun_preimage g C B) \<in> Tx "  
           apply (simp add: topological_space.open_set_def)   done
    from  a1 s15 s16 have s17: "(fun_preimage f C A)  \<union> (fun_preimage g C B) \<in> Tx "  
           apply (simp add:topological_space.union_in_T) done 
    from s17 s6 have s18 : "(fun_preimage h C X)\<in> Tx "  apply simp done
    from a1 s18 show ?thesis 
          apply (simp add:topological_space.open_set_def) done
qed

lemma pasting_lemma_3:
  "\<And>C. \<lbrakk>topological_space X Tx;
         topological_space Y Ty;
        X = A \<union>  B;
        topological_space.open_set Tx  A ; 
        topological_space.open_set Tx  B ;
        f: A \<rightarrow> Y;
        g: B \<rightarrow> Y;
        continuous f A (topological_space.subspace_topology Tx  A)  Y Ty ;
        continuous g B (topological_space.subspace_topology Tx  B)  Y Ty;
        \<And>x. \<lbrakk>x\<in> A \<inter> B\<rbrakk> \<Longrightarrow> f x = g x ;
        \<And>x. \<lbrakk>x\<in> A\<rbrakk> \<Longrightarrow>  h x = f x ;
        \<And>x. \<lbrakk>x\<in> B\<rbrakk> \<Longrightarrow> h x = g x ;
        topological_space.open_set Ty C
   \<rbrakk>  \<Longrightarrow> topological_space.open_set Tx (fun_preimage h C X) "   
apply (rule  pasting_lemma_2)
apply simp+
done
 


lemma pasting_lemma_open_set:
 assumes a1:  "topological_space X Tx"
 and     a2:  "topological_space Y Ty"
 and     a3:  "X = A \<union> B"
 and     a4:  "topological_space.open_set Tx  A" 
 and     a5:  "topological_space.open_set Tx  B"
 and     a6:  "f: A \<rightarrow> Y"
 and     a7:  "g: B \<rightarrow> Y"
 and     a8:  "continuous f A 
    (topological_space.subspace_topology Tx A) Y Ty"
 and     a9:  "continuous g B 
    (topological_space.subspace_topology Tx B) Y Ty"
 and     a10:  "\<And>x. \<lbrakk>x\<in> A \<inter> B\<rbrakk> \<Longrightarrow> f x = g x "
 and     a11: "\<And>x. \<lbrakk>x\<in> A\<rbrakk> \<Longrightarrow>  h x = f x "
 and     a12: "\<And>x. \<lbrakk>x\<in> B\<rbrakk> \<Longrightarrow> h x = g x "
 shows   "continuous h X Tx  Y Ty"


proof-
  from a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 have s1:
        "\<And>C. \<lbrakk> (topological_space.open_set Ty C)\<rbrakk> \<Longrightarrow> 
            topological_space.open_set Tx (fun_preimage h C X) "
        apply (rule  pasting_lemma_3) apply simp+ done
  from s1 have s2 : "\<forall>C. (topological_space.open_set Ty C) \<longrightarrow>  
          (topological_space.open_set Tx (fun_preimage h C X)) "
        apply simp done
   from a3 a6 a7 a10 a11 a12 have s3:"h \<in> X \<rightarrow>Y"  
        apply( simp add :Pi_def)  done
  from  a1 a2 s2 s3 show ?thesis  
        apply (simp add:  continuous_def) done
qed


lemma pasting_lemma_closed_set_1[simp]:
 assumes a1: "topological_space X Tx"
 and     a2: "topological_space Y Ty"
 and     a3: "X = A \<union> B"
 and     a4: "topological_space.closed_set X Tx A" 
 and     a5: "topological_space.closed_set X Tx B"
 and     a6: "f: A \<rightarrow> Y"
 and     a7: "g: B \<rightarrow> Y"
 and     a8: "continuous f A 
    (topological_space.subspace_topology Tx A) Y Ty"
 and     a9: "continuous g B 
    (topological_space.subspace_topology Tx B) Y Ty"
 and        a10: "\<And>x. \<lbrakk>x\<in> A \<inter> B\<rbrakk> \<Longrightarrow> f x = g x "
 and        a11: "\<And>x. \<lbrakk>x\<in> A\<rbrakk> \<Longrightarrow>  h x = f x "
 and        a12: "\<And>x. \<lbrakk>x\<in> B\<rbrakk> \<Longrightarrow> h x = g x "
 and        a13:" topological_space.closed_set Y Ty C"
 shows  "topological_space.closed_set X Tx  (fun_preimage h C X)"
proof-
    from a3 a6 a7 a10 a11 a12 have s1: "h \<in> X \<rightarrow>Y"  
        apply( simp add :Pi_def)  done
    from  a11    have s2:
       "{a. h a \<in> C \<and> a \<in> A} ={a. f  a \<in> C \<and> a \<in> A}"  
        apply (rule  pasting_lemma_1) 
        apply blast done
    from a12    have s3:
        "{a. h a \<in> C \<and> a \<in> B} ={a. g  a \<in> C \<and> a \<in> B}" 
        apply (rule  pasting_lemma_1) 
        apply blast done
    from  a3 a13 have s4 :
        "{a . h a \<in> C \<and> a \<in> X } = {a. h a \<in> C \<and>  a \<in> A} \<union> {a. h a \<in> C \<and> a \<in> B} " 
        apply blast done
    from  s2 s3 s4 have s5 :"{a . h a \<in> C \<and> a \<in> X } ={a. f  a \<in> C \<and> a \<in> A} \<union> {a. g  a \<in> C \<and> a \<in> B}"  
        apply simp done
    from  s4 s5 have   s6:  "fun_preimage h C X = (fun_preimage f C A) \<union> (fun_preimage g C B)" 
        apply (simp add:fun_preimage_def) done
    from a3 have s7:"A \<subseteq> X" apply blast done
    from a1 a3 s7  have s8: 
        "topological_space A (topological_space.subspace_topology Tx A) "  
        apply  (simp add:topological_space.subspace_is_top) done
    from a1 a4 a13 a8  s8 have s9:
         "topological_space.closed_set 
                A (topological_space.subspace_topology Tx A) 
               (fun_preimage f C A)"  
         apply (simp add:continuous_2_closed_set) done
    from  a1  a4 s7 s9 have s10: 
          "topological_space.closed_set X Tx (fun_preimage f C A)" 
          apply (simp add: sub_closed) done
    from a3 have s11:"B \<subseteq> X" 
          apply blast done
    from a1 a3 s11  have s12: 
         "topological_space B (topological_space.subspace_topology Tx B) "  
         apply  (simp add:topological_space.subspace_is_top) done
    from a1 a5 a13 a9  s12 have s13:
          "topological_space.closed_set 
               B (topological_space.subspace_topology Tx B) 
              (fun_preimage g C B)" 
           apply (simp add:continuous_2_closed_set) done
    from  a1  a5 s11 s13 have s14: 
          "topological_space.closed_set X Tx (fun_preimage g C B)" 
          apply (simp add: sub_closed) done
    from  a1 s10   have s15: "X - (fun_preimage f C A) \<in> Tx "  
          apply (simp add: topological_space.closed_set_def  
                           topological_space.open_set_def)   done
    from  a1 s14   have s16: "X - (fun_preimage g C B) \<in> Tx "  
          apply (simp add: topological_space.closed_set_def 
                           topological_space.open_set_def)   done
    from a1 s15 s16 have s17: 
         "(X - (fun_preimage f C A)) \<inter> (X - (fun_preimage g C B)) \<in> Tx " 
          apply (simp add:topological_space_def) done
    have s18: "(X - (fun_preimage f C A)) \<inter>  (X - (fun_preimage g C B))
                  =
               (X - ((fun_preimage f C A)  \<union>   (fun_preimage g C B))) " 
           apply blast done
   from s17 s18 have  s19: 
          "(X - ((fun_preimage f C A)  \<union>   (fun_preimage g C B))) \<in> Tx" 
            apply simp done
   from s19 s6 have s20 : "X -(fun_preimage h C X)\<in> Tx "  
            apply simp done
   have s21 : "(fun_preimage h C X) \<subseteq> X"
          apply  (simp add: fun_preimage_def) 
          apply blast done
    from a1 s20 s21 show ?thesis 
          apply (simp add:topological_space.closed_set_def 
                          topological_space.open_set_def) done
qed

lemma pasting_lemma_closed_set_2:
  "\<And>C. \<lbrakk>topological_space X Tx;
        topological_space Y Ty;
        X = A \<union>  B;
        topological_space.closed_set X Tx A; 
        topological_space.closed_set X Tx B;
        f: A \<rightarrow> Y;
        g: B \<rightarrow> Y;
        continuous f A (topological_space.subspace_topology Tx  A)  Y Ty ;
        continuous g B (topological_space.subspace_topology Tx  B)  Y Ty;
        \<And>x. \<lbrakk>x\<in> A \<inter> B\<rbrakk> \<Longrightarrow> f x = g x ;
        \<And>x. \<lbrakk>x\<in> A\<rbrakk> \<Longrightarrow>  h x = f x ;
        \<And>x. \<lbrakk>x\<in> B\<rbrakk> \<Longrightarrow> h x = g x ;
        topological_space.closed_set Y Ty C
   \<rbrakk>  \<Longrightarrow> topological_space.closed_set X Tx (fun_preimage h C X) "   
apply (rule  pasting_lemma_closed_set_1)
apply simp+
done
 
lemma pasting_lemma_closed_set:
 assumes a1: "topological_space X Tx"
 and     a2: "topological_space Y Ty"
 and     a3: "X = A \<union> B"
 and     a4: "topological_space.closed_set X Tx  A" 
 and     a5: "topological_space.closed_set X Tx  B"
 and     a6: "f: A \<rightarrow> Y"
 and     a7: "g: B \<rightarrow> Y"
 and     a8: "continuous f A 
   (topological_space.subspace_topology Tx A) Y Ty"
 and     a9:  "continuous g B 
   (topological_space.subspace_topology Tx B) Y Ty"
 and     a10: "\<And>x. \<lbrakk>x\<in> A \<inter> B\<rbrakk> \<Longrightarrow> f x = g x "
 and     a11: "\<And>x. \<lbrakk>x\<in> A\<rbrakk> \<Longrightarrow>  h x = f x "
 and     a12: "\<And>x. \<lbrakk>x\<in> B\<rbrakk> \<Longrightarrow> h x = g x "
 shows   "continuous h X Tx  Y Ty"
proof-
  from a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 have s1:
      "\<And>C. \<lbrakk> (topological_space.closed_set Y Ty  C)\<rbrakk> \<Longrightarrow> 
         topological_space.closed_set X Tx  (fun_preimage h C X)"
      apply (rule  pasting_lemma_closed_set_2)
      apply simp+ done
  from s1 have s2 : "\<forall>C. (topological_space.closed_set Y Ty C)
         \<longrightarrow>  (topological_space.closed_set X Tx (fun_preimage h C X)) " apply simp done
   from a3 a6 a7 a10 a11 a12 have s3:"h \<in> X \<rightarrow>Y"  apply( simp add :Pi_def)  done
  from  a1 a2 s2 s3 show ?thesis  apply (simp add:  closed_set_continuous) done
qed

end