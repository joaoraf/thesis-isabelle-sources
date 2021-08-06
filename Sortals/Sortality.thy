section \<open>Formal Characterization of Sortality\<close>

theory Sortality
  imports 
      Trimming 
      FiniteInstantiation 
      "../Identity/Identity"
begin

text \<^marker>\<open>tag bodyonly\<close> \<open>
  Our approach to the definition of sortality changes the perspective from
  trying to define sortality thorugh the existence of a suitable identity
  condition to defining non-sortality through the abstraction of the properties
  that identity instances of a substantial universal. We arrive at a formal
  definition that follows this strategy by using the \emph{trimming}
  operation.
  \<close>
text_raw \<open>\par\<close>
context finite_instantiation
begin

text \<^marker>\<open>tag bodyonly\<close> \<open>
  First, let's note that the permutability of particulars of \<open>\<Gamma>\<close> is
  preserved under trimming by a universal, i.e. a permutable particular
  of \<open>\<Gamma>\<close> is also a permutable particular of \<open>trim U\<close>:
\<close>
text_raw \<open>\par\<close>
lemma  permutables_preserved_under_trimming:
  fixes x and U :: 'u
  assumes A: \<open>x \<in> \<S>\<close> \<open>x \<notin> \<P>\<^sub>1\<^sub>!\<close>
  shows \<open>x \<notin> trim_non_permutables U\<close>
proof - 
  have A1: \<open>x \<in> \<P>\<close> using A by blast
  obtain \<phi> y where 
      B: \<open>\<phi> \<in> EndoMorphs\<^bsub>\<Gamma>\<^esub>\<close> \<open>y \<in> \<E>\<close> \<open>(\<phi> y = x) \<noteq> (y = x)\<close>
    using A(2)[THEN notE, OF non_permutables_I,OF A1 non_permutable_I] by blast
  have B1: \<open>y \<in> \<S>\<close> 
    using B(3,2) A(1) apply auto
    subgoal premises P
      using P(3,4)
      by (metis B(1) endomorphisms_iff particular_struct_endomorphism_def 
          particular_struct_morphism_def
          pre_particular_struct_morphism.morph_preserves_moments 
          ufo_particular_theory_sig.\<Gamma>_simps(3))
    done
  have \<open>\<phi> \<in> Perms\<^bsub>trim U\<^esub>\<close> using phi_in_trim_perm[OF B(1),of U] by simp
  then interpret I1: particular_struct_permutation \<open>trim U\<close> \<phi> by simp
  obtain B2: \<open>x \<in> I1.endurants\<close> \<open>y \<in> I1.endurants\<close> 
    using A(1) B1 I1.endurantI3 by auto
  let ?I1_\<Gamma> = \<open>trim U\<close>  
  have I1_src_\<Gamma>: \<open>I1.src.\<Gamma> = trim U\<close> using I1.src.\<Gamma>_simps by blast
  have C: \<open>\<phi> \<in> EndoMorphs\<^bsub>?I1_\<Gamma>\<^esub>\<close>     
    using I1.particular_struct_endomorphism_axioms by force  
  have D: \<open>trim_non_permutables U = I1.src.non_permutables\<close>
    by (simp only: trim_simps)
  show ?thesis    
    apply (simp only: D)
    apply (intro notI ; elim I1.src.non_permutables_E)
    subgoal premises P
      using I1.src.non_permutable_E[of x,simplified I1_src_\<Gamma>,
                                    OF P(2) C,of y,OF B2(2)] 
            B(3) by simp
    done
qed

text \<^marker>\<open>tag bodyonly\<close> \<open>
  Conversely, if a particular is non-permutable in the trimmed structure, it
  is also a non-permutable in \<open>\<Gamma>\<close>, i.e. it is identifiable in \<open>\<Gamma>\<close>:
\<close>
text_raw \<open>\par\<close>
lemma  non_permutables_under_trimming_are_the_identifiable:
  fixes x and U 
  assumes \<open>x \<in> \<S>\<close> \<open>x \<in> trim_non_permutables U\<close>
  shows \<open>x \<in> \<P>\<^sub>=\<close>
proof -
  have \<open>x \<in> \<P>\<^sub>1\<^sub>!\<close>
    using permutables_preserved_under_trimming[OF assms(1)] assms(2) 
    by metis
  then show ?thesis
    using identifiable_particulars_are_the_non_permutables
    by simp
qed

end

context iso_instantiation_sig
begin

text \<^marker>\<open>tag bodyonly\<close> \<open>
  We define the set of sortal universals as the set of substantial universals
  whose instances are non-permutable when trimmed by them. More specifically,
  a substantial universal \<open>U\<close> is a sortal just in case any instance of
  \<open>U\<close> is non-permutable in \<open>trim U\<close>. Formally, we have:
\<close>
text_raw \<open>\par\<close>
definition \<open>Sortals \<equiv> { U . U \<in> \<U>\<^sub>\<S> \<and> Insts U \<subseteq> trim_non_permutables U}\<close>

text \<^marker>\<open>tag bodyonly\<close> \<open>
  In other words, a sortal is a substantial universal that does not abstract enough details
  from its instances to the point that identification of the later becomes
  impossible. 

  Note that this definition does not require the existence of an identity
  condition, nor it implies that such an identity condition exists.
  Nevertheless, since permutability imply non-identifiability
  of particulars, the \emph{non-sortality} implies the impossibility of
  such an identity condition to exist, since the impossibility of constructing
  an identifying predicate for a specific instance implies that the 
  construction of a general identifying predicate for the set of instances is
  also impossible.

  Thus, the definition of sortality provided here is, in one hand, weaker than a
  characterization of sortality through the existence of an identity criteria.
  However, it is completely determinable from the model of the UFO theory of
  particulars itself., i.e. it's grounded solely on the model structure. In contrast,
  the usual characterization of sortality is grounded in the existence of a
  suitable predicate, an entity that is not necessarily present in a 
  particular structure, e.g. in those that languages are not represented.  
\<close>
text_raw \<open>\par\<close>
lemma  \<^marker>\<open>tag (proof) aponly\<close> SortalsI[intro!]:
  assumes \<open>U \<in> \<U>\<^sub>\<S>\<close> \<open>\<And>x w. x \<Colon>\<^bsub>w\<^esub> U \<Longrightarrow> x \<in> trim_non_permutables U\<close>
  shows \<open>U \<in> Sortals\<close>
  using assms by (auto simp: Sortals_def)

lemma  \<^marker>\<open>tag (proof) aponly\<close> SortalsE[elim!]:
  assumes \<open>U \<in> Sortals\<close>
  obtains \<open>U \<in> \<U>\<^sub>\<S>\<close> \<open>\<And>x w. x \<Colon>\<^bsub>w\<^esub> U \<Longrightarrow> x \<in> trim_non_permutables U\<close>
  using assms by (auto simp: Sortals_def)

lemma  \<^marker>\<open>tag (proof) aponly\<close> SortalsD:
  assumes \<open>U \<in> Sortals\<close>
  shows \<open>U \<in> \<U>\<^sub>\<S>\<close> \<open>\<And>x w. x \<Colon>\<^bsub>w\<^esub> U \<Longrightarrow> x \<in> trim_non_permutables U\<close>
  using assms by auto

lemma  \<^marker>\<open>tag (proof) aponly\<close> sortals_are_universals: \<open>Sortals \<subseteq> \<U>\<close>
  by blast

lemma  \<^marker>\<open>tag (proof) aponly\<close> sortals_are_subst_universals: \<open>Sortals \<subseteq> \<U>\<^sub>\<S>\<close>
  by blast

end

context finite_instantiation
begin

text \<^marker>\<open>tag bodyonly\<close> \<open>
  As expected from the definition, all instances of a sortal are identifiable:
\<close>
text_raw \<open>\par\<close>
lemma  sortals_instances_are_identifiable: 
  assumes \<open>U \<in> Sortals\<close> \<open>x \<in> Insts U\<close>
  shows \<open>x \<in> \<P>\<^sub>=\<close>
proof -
  obtain A: \<open>U \<in> \<U>\<^sub>\<S>\<close> \<open>U \<in> \<U>\<close>  using assms(1) by blast
  then have B: \<open>x \<in> \<S>\<close> using assms(2)  \<U>\<^sub>\<S>_insts by blast
  show ?thesis 
    apply (intro 
            non_permutables_under_trimming_are_the_identifiable[of x U] A B)
    using assms(2) SortalsD[OF assms(1)] by blast
qed

end

end

