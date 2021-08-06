subsection \<open>Identity Characterization Equivalences\<close>

theory Identity
  imports Correspondence "../ParticularStructures/StructuralPropertiesTheorems"
  Individuality AnchoringAndIdentifiability
        
begin

context ufo_particular_theory
begin

text \<^marker>\<open>tag bodyonly\<close> \<open>
  Here is a summary of the logical equivalences between the concepts that can
  be used to characterize identity:
\<close>
text_raw \<open>\par\<close>
lemma \<^marker>\<open>tag (proof) aponly\<close> identifiable_particulars_are_individuals:  
    \<open>\<P>\<^sub>= \<subseteq> \<P>\<^sub>i\<^sub>n\<^sub>d\<close>  
  by (simp add: identifiables_are_the_non_permutables non_permutables_are_non_collapsible)

theorem  identifiable_particulars_are_the_non_permutables: 
    \<open>\<P>\<^sub>= = \<P>\<^sub>1\<^sub>!\<close>
  using identifiables_are_the_non_permutables .

theorem  identifiable_particulars_are_the_isomorphically_unique:
    \<open>\<P>\<^sub>= = \<P>\<^sub>\<simeq>\<^sub>!\<close>
  using identifiables_are_the_im_uniques .

theorem identifiable_particulars_are_the_anchored_particulars:
    \<open>\<P>\<^sub>= = \<P>\<^sub>\<down>\<close>
  by (simp add: anchored_are_the_non_permutable 
                identifiables_are_the_im_uniques 
                non_permutable_particulars_are_the_unique_particulars) 

end

end
