theory FuncSetExtra
  imports Main Common "HOL-Library.FuncSet"
begin

abbreviation compose_restrict  (\<open>_ \<circ>\<^bsub>_\<^esub>/ _\<close> [56,1,55] 55) where
  \<open>f \<circ>\<^bsub>X\<^esub> g \<equiv> compose X f g\<close>

definition id_on :: \<open>'a set \<Rightarrow> 'a \<Rightarrow> 'a\<close>  where
  \<open>id_on X x \<equiv> if x \<in> X then x else undefined\<close>

lemma id_on_eq[simp]: \<open>x \<in> X \<Longrightarrow> id_on X x = x\<close>
             \<open>x \<notin> X \<Longrightarrow> id_on X x = undefined\<close>
  by (auto simp: id_on_def)

lemma id_on_eq_restrict: \<open>id_on X = restrict id X\<close>
  by (auto simp: id_on_def)

lemma id_on_injective[intro!,simp]: \<open>inj_on (id_on X) X\<close>
  apply (intro inj_onI)
  by simp

lemma id_on_surjective[simp]: \<open>(id_on X) ` X = X\<close>
  by auto

lemma id_on_bij_betw[intro!,simp]: \<open>bij_betw (id_on X) X X\<close>
  using id_on_injective id_on_surjective 
  by (metis inj_on_imp_bij_betw)

lemma id_on_inv_into[simp]: \<open>x \<in> X \<Longrightarrow> inv_into X (id_on X) x = x\<close>  
  by (simp add: inv_into_f_eq)

definition Inv where 
  \<open>Inv X f x \<equiv> if x \<in> f ` X then inv_into X f x else undefined\<close>

lemma Inv_eq: \<open>\<lbrakk> inj_on f X ; y \<in> X ; f y = x \<rbrakk> \<Longrightarrow> Inv X f x = y\<close>
  apply (auto simp: Inv_def)  
  by (simp add: inj_onD)

lemma Inv_inj_surj: \<open>inj_on f X \<Longrightarrow> Inv X f ` (f ` X)  = X\<close>
  by (auto simp: Inv_def)

lemma Inv_surj_inj: \<open>inj_on (Inv X f) (f ` X) \<close>
  apply (intro inj_onI)
  apply (auto simp: Inv_def)  
  by (metis f_inv_into_f imageI)

lemma id_on_eq_restric_inv[simp]: \<open>Inv X (id_on X) = id_on X\<close>
  by (auto simp: Inv_def)

lemma id_on_id_on_comp[simp]: \<open>id_on X \<circ>\<^bsub>Y\<^esub> id_on Y = id_on (X \<inter> Y)\<close>
  apply (intro ext)
  subgoal for x
    by (cases \<open>x \<in> Y\<close> ; simp add: compose_def id_on_def)
  done

lemma id_on_in_extensional[intro!,simp]: \<open>id_on X \<in> extensional X\<close>
  by (auto simp: extensional_def)

lemma comp_map_associative:
  assumes \<open>\<phi>\<^sub>2\<^sub>1 ` X \<subseteq> Y\<close>
  shows \<open>\<phi>\<^sub>3\<^sub>4 \<circ>\<^bsub>X\<^esub> (\<phi>\<^sub>2\<^sub>3 \<circ>\<^bsub>X\<^esub> \<phi>\<^sub>2\<^sub>1) = (\<phi>\<^sub>3\<^sub>4 \<circ>\<^bsub>Y\<^esub> \<phi>\<^sub>2\<^sub>3) \<circ>\<^bsub>X\<^esub> \<phi>\<^sub>2\<^sub>1\<close>
proof -
  have A: \<open>\<phi>\<^sub>2\<^sub>1 x \<in> Y\<close> if \<open>x \<in> X\<close> for x
    using that assms by auto
  show ?thesis
    by (intro ext ; auto simp: compose_def A)
qed    

lemma inj_comp_map[intro!]:
  assumes \<open>inj_on \<phi>\<^sub>1 X\<close> \<open>inj_on \<phi>\<^sub>2 (\<phi>\<^sub>1 ` X)\<close>
  shows \<open>inj_on (\<phi>\<^sub>2 \<circ>\<^bsub>X\<^esub> \<phi>\<^sub>1) X\<close>
  using assms
  by (meson inj_on_compose inj_on_imp_bij_betw)

lemma map_comp_img_eq_comp_imp:
  assumes \<open>Y \<subseteq> X\<close> 
  shows \<open>(g \<circ>\<^bsub>X\<^esub> f) ` Y = (g \<circ> f) ` Y\<close>
  using assms 
  by (smt (verit, best) comp_def compose_eq image_cong in_mono)

lemma Inv_scope[simp,intro!]: \<open>Inv X f \<in> f ` X \<rightarrow> X\<close>
  apply (auto simp: Inv_def)  
  by (simp add: inv_into_into)

lemma f_Inv_eq[simp]: \<open>x \<in> f ` X \<Longrightarrow> f (Inv X f x) = x\<close>
  by (auto simp: Inv_def f_inv_into_f)  

lemma Inv_f_eq[simp]: \<open>\<lbrakk> inj_on f X ; y \<in> X \<rbrakk> \<Longrightarrow> Inv X f (f y) = y\<close>
  by (auto simp: Inv_def)

lemma Inv_bij_betw[intro!,simp]: 
  assumes  \<open>inj_on f X\<close>
  shows \<open>bij_betw (Inv X f) (f ` X) X\<close>  
  using assms by (intro bij_betwI[of _ _ _ f] ; simp?)

lemma image_Inv_cancel:
  assumes \<open>f ` A = B\<close> \<open>C \<subseteq> B\<close>
  shows \<open>f ` Inv A f ` C = C\<close> 
  by (metis Inv_def assms(1) assms(2) image_cong 
            image_inv_into_cancel subset_iff)

lemma Inv_scope':
  assumes \<open>inj_on f X\<close> \<open>Y \<subseteq> X\<close> \<open>f \<in> Y \<rightarrow> f ` Y\<close>
  shows \<open>Inv X f \<in> f ` Y \<rightarrow> Y\<close>
proof
  fix x
  assume \<open>x \<in> f ` Y\<close>
  then obtain y where \<open>y \<in> Y\<close> \<open>f y = x\<close> by blast
  then have \<open>y \<in> X\<close> using assms by blast
  then show \<open>Inv X f x \<in> Y\<close>
    using \<open>f y = x\<close> Inv_f_eq[of f X y] assms(1) \<open>y \<in> Y\<close> 
    by simp
qed        

lemma Inv_extensional: \<open>Inv X f \<in> extensional (f ` X)\<close>
  by (auto simp: Inv_def extensional_def)

lemma inj_on_map_comp_imageI2: \<open>inj_on (g \<circ>\<^bsub>A\<^esub> f) A \<Longrightarrow> inj_on f A\<close>
  apply (intro inj_on_imageI2[of g f A])  
  by (simp add: compose_eq inj_on_def)

lemma id_on_extensional: \<open>\<lbrakk> Y \<subseteq> X ; Y \<subseteq> Z \<rbrakk> \<Longrightarrow> id_on X \<in> Y \<rightarrow> Z\<close>  
  by (simp add: in_mono)

lemma id_on_img: \<open>Y \<subseteq> X \<Longrightarrow> id_on X ` Y = Y\<close>
  by (auto simp: id_on_def)

lemma map_comp_img: 
  assumes \<open>Y \<subseteq> X\<close>
  shows \<open>(g \<circ>\<^bsub>X\<^esub> f) ` Y = g ` f ` Y\<close>
  using assms
  by (simp add: image_comp map_comp_img_eq_comp_imp)

lemma funcsetI:
  assumes \<open>\<And>x. x \<in> X \<longleftrightarrow> f x \<in> Y\<close>
  shows \<open>f \<in> X \<rightarrow> Y\<close>
  using assms by auto

lemma inj_on_zf_to_delimited_func:  
  assumes \<open>\<exists>f :: 'a \<Rightarrow> ZF. inj_on f A\<close>
  obtains g :: \<open>'a \<Rightarrow> ZF\<close> where \<open>inj_on g A\<close> \<open>g \<in> extensional A\<close> \<open>undefined \<notin> g ` A\<close>
proof -
  obtain f :: \<open>'a \<Rightarrow> ZF\<close> where \<open>inj_on f A\<close> using assms by blast
  define f\<^sub>1 where \<open>f\<^sub>1 x \<equiv> Opair undefined (f x)\<close> for x
  have f1_inj: \<open>inj_on f\<^sub>1 A\<close>
    using f\<^sub>1_def \<open>inj_on f A\<close>    
    by (simp add: Opair inj_on_def) 
  define g where \<open>g x \<equiv> if x \<in> A then f\<^sub>1 x else undefined\<close> for x
  have g_inj: \<open>inj_on g A\<close>
    apply (intro inj_onI ; simp add: g_def)
    using f1_inj inj_onD by metis
  have g_ext: \<open>g \<in> extensional A\<close>
    by (auto simp: g_def extensional_def)
  have g_undef: \<open>undefined \<notin> g ` A\<close>
    apply (intro notI ; elim imageE exE ; simp add: g_def f\<^sub>1_def)    
    by (metis Elem_Opair_exists notsym_Elem)
  then show ?thesis using g_inj g_ext that by blast
qed

lemma inj_zf_to_delimited_func:
  assumes \<open>\<exists>f :: 'a \<Rightarrow> ZF. inj f\<close>
  obtains g :: \<open>'a \<Rightarrow> ZF\<close> where \<open>inj_on g A\<close> \<open>g \<in> extensional A\<close> \<open>undefined \<notin> g ` A\<close>
  using assms inj_on_zf_to_delimited_func  
  by (metis inj_eq inj_on_def)
    
end  