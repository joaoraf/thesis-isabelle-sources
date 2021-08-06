text_raw \<open>\subsection[Identity-Related Dependency Relations]{Identity-Related Dependency Relations\isalabel{subsec:identification dependency}}\<close>

theory IdentificationDependence
  imports AnchoringSets
begin

context ufo_particular_theory
begin

(* abbreviation anchoring_dep :: \<open>'p \<Rightarrow> 'p \<Rightarrow> bool\<close> (\<open>ad\<close>)
  where \<open>ad x y \<equiv> y \<in> \<Union>\<A>\<^bsub>x\<^esub>\<close> *)
(*
abbreviation mandatory_anchoring_dep :: \<open>'p \<Rightarrow> 'p \<Rightarrow> bool\<close> (\<open>mad\<close>)
  where \<open>mad x y \<equiv> y \<in> IdCore\<^bsub>x\<^esub>\<close>
*)
(*
abbreviation optional_anchoring_dep :: \<open>'p \<Rightarrow> 'p \<Rightarrow> bool\<close> (\<open>oad\<close>)
  where \<open>oad x y \<equiv> y \<in> \<Union>(IdComps\<^bsub>x\<^esub>)\<close>
*)

(*
lemma \<^marker>\<open>tag (proof) aponly\<close> ad_refl[intro!]: 
  assumes \<open>x \<in> \<P>\<^sub>\<Down>\<close>
  shows \<open>ad x x\<close> 
  using assms apply (elim minimallyAnchored_E)  
  subgoal for y \<Gamma>\<^sub>x \<phi>
    apply (intro UnionI[of \<open>\<phi> ` particulars \<Gamma>\<^sub>x\<close>] anchorSets_I[of y] ; simp?)
    apply (intro rev_image_eqI[of y] ; elim minimallyAnchorsE)
    subgoal by blast
    subgoal
      apply (elim anchorsE)      
      using particular_struct_injection_def by blast
    done
  done
*)

(*
lemma \<^marker>\<open>tag (proof) aponly\<close> anchoring_dep_cases[cases pred]:
  assumes \<open>ad x y\<close>
  obtains (mandatory) \<open>mad x y\<close> |
          (optional) \<open>oad x y\<close>
  by (meson DiffI Union_iff assms identityComplementsI1)
*)
(* definition \<^marker>\<open>tag aponly\<close> weak_identification_dep :: \<open>'p \<Rightarrow> 'p \<Rightarrow> bool\<close> (\<open>wid\<close>)
  where \<open>wid x y \<longleftrightarrow> (\<exists>X \<in> \<A>\<^bsub>x\<^esub>. \<exists>Y \<in> \<A>\<^bsub>y\<^esub>. Y \<subseteq> X)\<close> *)

text \<^marker>\<open>tag bodyonly\<close> \<open>
  Using the concept of anchor sets, we can define a notion of
  \emph{identification dependence}. We call \<open>y\<close> an 
  idenfication dependence of \<open>x\<close>, written as \<open>IdDep x y\<close>,
  just in case all anchoring sets of \<open>y\<close> are also anchoring
  sets of \<open>x\<close>. In other words, it is impossible to identify
  \<open>x\<close> without also identifying \<open>y\<close>. If the converse does
  not hold, then we can say that it is necessary to identify
  \<open>y\<close> before indentifying \<open>x\<close>. Formally, we have:
\<close>

definition identification_dep :: \<open>'p \<Rightarrow> 'p \<Rightarrow> bool\<close> (\<open>IdDep\<close>)
  where \<open>IdDep x y \<longleftrightarrow> (\<forall>X \<in> \<A>\<^bsub>x\<^esub>. \<exists>Y \<in> \<A>\<^bsub>y\<^esub>. Y \<subseteq> X)\<close>

(* lemma \<^marker>\<open>tag (proof) aponly\<close> weak_identification_dep_I[intro!]:
  assumes \<open>X \<in> \<A>\<^bsub>x\<^esub>\<close> \<open>Y \<in> \<A>\<^bsub>y\<^esub>\<close> \<open>Y \<subseteq> X\<close>
  shows \<open>wid x y\<close>
  using assms by (simp add: weak_identification_dep_def ; metis) *)

(* lemma \<^marker>\<open>tag (proof) aponly\<close> weak_identification_dep_E[elim!]:
  assumes \<open>wid x y\<close>
  obtains X Y where \<open>X \<in> \<A>\<^bsub>x\<^esub>\<close> \<open>Y \<in> \<A>\<^bsub>y\<^esub>\<close> \<open>Y \<subseteq> X\<close>
  using assms by (simp add: weak_identification_dep_def ; metis) *)

lemma \<^marker>\<open>tag (proof) aponly\<close> identification_dep_I[intro!]:
  assumes \<open>\<And>X. X \<in> \<A>\<^bsub>x\<^esub> \<Longrightarrow> \<exists>Y \<in> \<A>\<^bsub>y\<^esub>. Y \<subseteq> X\<close>
  shows \<open>IdDep x y\<close>
  using assms 
  by (simp only: identification_dep_def ; metis)

lemma \<^marker>\<open>tag (proof) aponly\<close> identification_dep_E[elim]:
  assumes \<open>IdDep x y\<close> \<open>X \<in> \<A>\<^bsub>x\<^esub>\<close>
  obtains Y where \<open>Y \<in> \<A>\<^bsub>y\<^esub>\<close> \<open>Y \<subseteq> X\<close>  
  using assms 
  by (simp only: identification_dep_def ; metis)

(* lemma \<^marker>\<open>tag (proof) aponly\<close> strong_imp_weak_identification_dep:
  assumes \<open>x \<in> \<P>\<^sub>\<Down>\<close> \<open>IdDep x y\<close>
  shows \<open>wid x y\<close>
  using assms apply (elim minimallyAnchored_to_AnchorSet )
  subgoal for X
    apply (elim identification_dep_E[of _ _ X] ; simp?)
    subgoal for Y
      by (intro weak_identification_dep_I[of X _ Y] ; simp)
    done
  done *)

text \<^marker>\<open>tag bodyonly\<close> \<open>
  Identification dependence is a \emph{pre-order}, i.e. it is
  a reflexive and transitive relation:
\<close>

lemma identification_dep_refl[intro!]: \<open>IdDep x x\<close>
  apply (intro identification_dep_I)
  subgoal for X
    by (intro bexI[of _ X] ; simp)
  done

(* lemma \<^marker>\<open>tag (proof) aponly\<close> weak_identificaition_dep_refl[intro!]:
  assumes \<open>x \<in> \<P>\<^sub>\<Down>\<close>
  shows \<open>wid x x\<close>
  using assms strong_imp_weak_identification_dep
    identification_dep_refl
  by metis *)

(* lemma \<^marker>\<open>tag (proof) aponly\<close> weak_identificaition_dep_trans_strong:
  assumes \<open>wid x y\<close> \<open>IdDep y z\<close>
  shows \<open>wid x z\<close>
  using assms 
  apply (elim weak_identification_dep_E)
  subgoal for X Y
    apply (elim identification_dep_E[of _ _ Y] ; simp?)
    subgoal for Z
      by (intro weak_identification_dep_I[of X _ Z] ; simp)
    done
  done
*)

lemma identification_dep_trans[trans]:          
  assumes \<open>IdDep x y\<close> \<open>IdDep y z\<close>
  shows \<open>IdDep x z\<close>
  using assms 
  using assms apply (simp add: identification_dep_def)
  apply (intro ballI)  
  subgoal premises P for X
    using P(1)[rule_format,OF P(3)] apply (elim bexE)
    subgoal premises Q for Y
      using P(2)[rule_format,OF Q(1)] apply (elim bexE)
      subgoal for Z
        apply (intro bexI[of _ Z])
        using P Q by simp+
      done
    done
  done

end

end