theory PartialFunctions
  imports Main
begin

type_synonym ('a,'b) pfunc = \<open>'a \<Rightarrow> 'b option\<close> (infixl \<open>\<mapsto>\<close> 55)

definition id_on :: \<open>'a set \<Rightarrow> 'a \<mapsto> 'a\<close> where
  \<open>id_on X x \<equiv> if x \<in> X then Some x else None\<close>

definition map_inv :: \<open>('a \<mapsto> 'b) \<Rightarrow> 'b \<mapsto> 'a\<close> where
  \<open>map_inv f x \<equiv> 
      if x \<in> ran f then Some (inv_into (dom f) f (Some x)) else None\<close>

abbreviation minj :: \<open>('a \<mapsto> 'b) \<Rightarrow> bool\<close> where
  \<open>minj f \<equiv> inj_on f (dom f)\<close>

lemma id_on_eq_I1: \<open>x \<in> X \<Longrightarrow> id_on X x = Some x\<close>
  by (auto simp: id_on_def)

lemma id_on_eq_I2: \<open>x \<notin> X \<Longrightarrow> id_on X x = None\<close>
  by (auto simp: id_on_def)

lemma id_on_eq_cases[cases pred]:
  assumes \<open>id_on X x = y\<close>
  obtains (none) \<open>x \<notin> X\<close> \<open>y = None\<close> |
          (some) \<open>x \<in> X\<close> \<open>y = Some x\<close>
  using assms
  by (cases \<open>x \<in> X\<close> ; auto simp: id_on_def)

lemma id_on_comp_left: 
  assumes \<open>ran f \<subseteq> X\<close> 
  shows \<open>id_on X \<circ>\<^sub>m f = f\<close>
  apply (intro ext ; simp add: map_comp_def id_on_def)
  using assms
  by (metis id_on_def option.case_eq_if option.exhaust_sel ranI subsetD)
  

lemma id_on_comp_right: 
  assumes \<open>dom f \<subseteq> X\<close> 
  shows \<open>f \<circ>\<^sub>m id_on X = f\<close>
  apply (intro ext ; simp add: map_comp_def id_on_def)
  using assms  
  by (metis domIff subsetD)

lemma id_on_dom[simp]: \<open>dom (id_on X) = X\<close>
  by (auto simp: id_on_def dom_def)  

lemma id_on_ran[simp]: \<open>ran (id_on X) = X\<close>
  by (auto simp: id_on_def ran_def)  
  
lemma id_on_unique:
  fixes f :: \<open>'a \<Rightarrow> 'a option\<close>
  assumes \<open>ran f = dom f\<close>
          \<open>\<And>g :: 'a \<Rightarrow> 'a option. ran g \<subseteq> dom f \<Longrightarrow> f \<circ>\<^sub>m g = g\<close> 
          \<open>\<And>g :: 'a \<Rightarrow> 'a option. ran f \<subseteq> dom g \<Longrightarrow> g \<circ>\<^sub>m f = g\<close>
  shows \<open>f = id_on (dom f)\<close>
proof -
  have f_inj: \<open>inj_on f (dom f)\<close>
  proof (rule ccontr)
    assume \<open>\<not> inj_on f (dom f)\<close>
    then obtain x y 
      where A: \<open>x \<in> dom f\<close> \<open>y \<in> dom f\<close>
               \<open>x \<noteq> y\<close> \<open>f x = f y\<close>      
      by (meson inj_onI)
    then consider \<open>f x \<noteq> Some x\<close> | \<open>f y \<noteq> Some y\<close> 
      by fastforce
    then obtain z where z: \<open>z \<in> dom f\<close> \<open>f z \<noteq> Some z\<close>
      using A by metis
    have B: \<open>f \<circ>\<^sub>m id_on (dom f) \<noteq> id_on (dom f)\<close>
    proof
      assume \<open>f \<circ>\<^sub>m id_on (dom f) = id_on (dom f)\<close>
      then have \<open>(f \<circ>\<^sub>m id_on (dom f)) z = id_on (dom f) z\<close> by simp
      then have \<open>f z = id_on (dom f) z\<close> 
        using id_on_comp_right[of f \<open>dom f\<close>] by simp
      then have \<open>f z = Some z\<close>
        using \<open>z \<in> dom f\<close> id_on_eq_I1 by simp
      then show False using \<open>f z \<noteq> Some z\<close> by simp
    qed
    have \<open>f \<circ>\<^sub>m id_on (dom f) = id_on (dom f)\<close>
      by (intro assms(2) ; simp?)
    then show False using B by simp
  qed
  then have inv_left: \<open>inv_into (dom f) f (f x) = x\<close> if \<open>x \<in> dom f\<close> for x
    using inv_into_f_f f_inj that by metis
  define g where 
      \<open>g x \<equiv> if x \<in> dom f then Some (inv_into (dom f) f (Some x)) else None\<close> 
    for x
  have not_in_dom_none: \<open>x \<notin> dom f \<Longrightarrow> f x = None\<close> for x
    by auto
  have R1: \<open>g \<circ>\<^sub>m f = id_on (dom f)\<close>
    apply (intro ext ; simp add: g_def map_comp_def)
    subgoal for x
      apply (cases \<open>x \<in> dom f\<close>)
      subgoal premises x_in_dom
        using x_in_dom apply (simp add: dom_def id_on_def)
        apply (elim exE ; simp add: g_def ; auto)
        subgoal premises P for y z
          by (intro inv_left[of x,simplified P(1)] x_in_dom)
        subgoal premises P for y
          using x_in_dom 
          by (metis P assms(1) domD ranI)
        done
      subgoal premises x_not_in_dom
        by (simp add: not_in_dom_none[OF x_not_in_dom] 
                       id_on_def x_not_in_dom)
      done
    done
  have R2: \<open>ran f \<subseteq> dom g\<close>    
    by (simp add: assms(1) domI g_def subset_iff)
  have \<open>g = id_on (dom f)\<close> 
    using R1 assms(3)[OF R2] by simp
  then have R3: \<open>id_on (dom f) \<circ>\<^sub>m f = id_on (dom f)\<close> 
    using R1 by simp
  have R4: \<open>id_on (dom f) \<circ>\<^sub>m f = f\<close>
    using id_on_comp_left[of f \<open>dom f\<close>] assms(1) by simp
  then show \<open>f = id_on (dom f)\<close> using R3 by simp
qed


lemma id_on_minj[intro!,simp]: \<open>minj (id_on X)\<close>
  by (intro inj_onI ; simp ; simp add: id_on_def)

lemma id_on_inj_on[intro!,simp]: \<open>inj_on (id_on X) X\<close>
  by (intro inj_onI ; simp add: id_on_def)

lemma map_inv_id_on[simp]: \<open>map_inv (id_on X) = id_on X\<close>
  apply (intro ext ; simp add: map_inv_def id_on_def; safe)
  subgoal for x    
    by (intro inv_into_f_f[of \<open>id_on X\<close> \<open>X\<close>,of x,simplified id_on_eq_I1]
          ; simp)
  done

lemma map_inv_id_on_comp[simp]: \<open>map_inv \<circ> id_on = id_on\<close>
  by auto

lemma map_image_eq_ran[simp]: \<open>f ` dom f = Some ` ran f\<close>
  apply (intro set_eqI iffI ; (elim imageE)?)
  subgoal for x y
    apply (simp add: dom_def ran_def; elim exE ; hypsubst_thin ; simp)
    by (intro imageI ; simp ; blast)
  subgoal for x y
    apply (simp add: ran_def ; elim exE ; hypsubst_thin)    
    subgoal for z
      by (intro rev_image_eqI[of z] ; (simp add: dom_def)?)
    done
  done
            
lemma minj_to_bijI[intro!]: 
  assumes \<open>minj f\<close>
  shows \<open>bij_betw f (dom f) (Some ` ran f)\<close>    
  using assms inj_on_imp_bij_betw[of f \<open>dom f\<close>]
  by simp

lemma minj_to_bij_iff[simp]:
  \<open>bij_betw f (dom f) (Some ` ran f) \<longleftrightarrow> minj f\<close>
  apply auto  
  using bij_betw_imp_inj_on by blast

lemma map_comp_in_dom_eq: \<open>x \<in> dom f \<Longrightarrow> (g \<circ>\<^sub>m f) x = g (the (f x))\<close>
  by (auto simp: map_comp_def)

lemma map_comp_not_in_dom_eq: \<open>x \<notin> dom f \<Longrightarrow> (g \<circ>\<^sub>m f) x = None\<close>
  by (simp add: map_comp_def dom_def)

lemmas map_comp_simps = map_comp_in_dom_eq map_comp_not_in_dom_eq

lemma inj_on_the[intro!,simp]: \<open>inj_on the (Some ` UNIV)\<close>
  by (intro inj_onI ; (elim imageE)? ; simp)

lemma id_on_univ_eq_some[simp]: \<open>id_on UNIV = Some\<close>
  by (auto simp: id_on_def)

lemma id_on_comp_int[simp]: \<open>id_on X \<circ>\<^sub>m id_on Y = id_on (X \<inter> Y)\<close>
  by (intro ext ; simp add: id_on_def map_comp_def)

lemma the_some_inv: \<open>inv_into (Some ` UNIV) the = Some\<close>
  apply (intro ext)
  by (intro inv_into_f_eq inj_on_the ; simp)

lemma Some_UNIV_eq: \<open>Some ` UNIV = UNIV - {None}\<close>
  apply (auto)  
  using notin_range_Some by blast

lemma map_in_on_cases[cases pred]:
  assumes \<open>inj_on f X\<close>
  obtains (subset_dom) \<open>X \<subseteq> dom f\<close> |
          (unique_out) x where \<open>x \<notin> dom f\<close> \<open>x \<in> X\<close> \<open>X - {x} \<subseteq> dom f\<close>
proof -
  have T1: \<open>\<exists>!x. x \<notin> dom f \<and> x \<in> X \<and> X - {x} \<subseteq> dom f\<close> if as: \<open>\<not> X \<subseteq> dom f\<close>
  proof -
    obtain x where A: \<open>x \<in> X\<close> \<open>x \<notin> dom f\<close>
      using as by blast      
    have fx[simp]: \<open>f x = None\<close> using A(2) by auto
    have X_eq: \<open>X = insert x (X \<inter> dom f)\<close>
    proof (safe ; (simp add: A(1))?)
      fix y 
      assume B: \<open>y \<in> X\<close> \<open>y \<noteq> x\<close> 
      show \<open>\<exists>z. f y = Some z\<close>
      proof (rule ccontr ; simp)
        assume \<open>f y = None\<close>
        then have \<open>f x = f y\<close> by simp
        then have \<open>y = x\<close> using A(1) B(1) assms inj_onD by metis
        then show False using B(2) by simp
      qed      
    qed
    have R1: \<open>X - {x} \<subseteq> dom f\<close>
      apply (subst X_eq)
      by (intro subsetI ; simp)
    have R2: \<open>\<exists>z. f y = Some z\<close> 
      if B: \<open>y \<noteq> x\<close> \<open>y \<in> X\<close> \<open>X - {y} \<subseteq> dom f\<close> for y
    proof -
      have \<open>y \<in> dom f\<close> using X_eq B(1,2) by blast
      then show ?thesis by blast
    qed
    
    show ?thesis
      by (intro ex1I[of _ x] ; (simp add: A R1)? ; safe
          ; (metis R2)?)    
  qed
  show ?thesis
    using T1 that by meson
qed

lemma dom_comp_subset: \<open>dom (g \<circ>\<^sub>m f) \<subseteq> dom f\<close>
  apply (auto simp: map_comp_def)
  subgoal for x y
    by (cases \<open>f x\<close> ; simp)
  done

lemma \<open>inj_on (g \<circ>\<^sub>m f) X \<longleftrightarrow> inj_on f X \<and> inj_on g (the ` f ` X)\<close>
proof (auto)
  show \<open>inj_on f X\<close> if as: \<open>inj_on (g \<circ>\<^sub>m f) X\<close>
  proof
    fix x y
    assume A: \<open>x \<in> X\<close> \<open>y \<in> X\<close> \<open>f x = f y\<close>   
    have y_dom_x_dom[simp]: \<open>y \<in> dom (g \<circ>\<^sub>m f) \<longleftrightarrow> x \<in> dom (g \<circ>\<^sub>m f)\<close>
      using A(3) by (cases \<open>f x\<close> ; cases \<open>f y\<close> ; simp add: dom_def)
    have R: \<open>x = y\<close> if as1: \<open>x \<in> dom (g \<circ>\<^sub>m f)\<close>
    proof -
      obtain C: \<open>x \<in> dom f\<close> \<open>y \<in> dom f\<close>
        using as1 y_dom_x_dom dom_comp_subset[of g f] by blast
      have D1: \<open>(g \<circ>\<^sub>m f) x = g (the (f x))\<close> 
        using C(1) map_comp_in_dom_eq by force
      have D2: \<open>(g \<circ>\<^sub>m f) y = g (the (f y))\<close> 
        using C(2) map_comp_in_dom_eq by force
      then have \<open>(g \<circ>\<^sub>m f) x = (g \<circ>\<^sub>m f) y\<close> using D1 A(3) by simp      
      then show \<open>x = y\<close> using as inj_onD A by metis
    qed
    show  \<open>x = y\<close>  
      using as 
    proof (cases)
      case subset_dom  
      then show \<open>x = y\<close>
         using subsetD R A(1) by metis    
    next
      case (unique_out z)
      { fix q
        assume \<open>q \<in> X\<close>
        then consider (outlier) \<open>q = z\<close> | (inside) \<open>q \<in> dom (g \<circ>\<^sub>m f)\<close>          
          by (metis as domIff inj_on_eq_iff unique_out(1) unique_out(2))
      }
      note inX_cases[consumes 1,case_names outlier inside,cases set] = this
      show ?thesis
        apply (insert \<open>x \<in> X\<close> ; cases x rule: inX_cases ; 
               insert \<open>y \<in> X\<close> ; cases y rule: inX_cases ; (simp add: A unique_out)?)
        subgoal using unique_out(1) y_dom_x_dom by metis
        using R by metis
    qed
  qed     
  show \<open>inj_on g (the ` f ` X)\<close> if as: \<open>inj_on (g \<circ>\<^sub>m f) X\<close>
  proof (intro inj_onI ; elim imageE ; simp ; hypsubst_thin
        ; rename_tac x y)
    fix x y
    assume A: \<open>g (the (f x)) = g (the (f y))\<close> \<open>x \<in> X\<close> \<open>y \<in> X\<close>
    have \<open>(g \<circ>\<^sub>m f) x = g (the (f x))\<close> 
      using map_comp_in_dom_eq A(2) by simp
    show \<open>the (f x) = the (f y)\<close>
    using as   proof (cases)
    case subset_dom     
    show ?thesis
    proof (intro inj_onI ; elim imageE ; simp ; hypsubst_thin
        ; rename_tac x y)
      fix x y
      assume as: \<open>g (the (f x)) = g (the (f y))\<close> \<open>x \<in> X\<close> \<open>y \<in> X\<close> 
      then obtain x\<^sub>1 y\<^sub>1 where A: \<open>f x\<^sub>1 = Some x\<close> \<open>f y\<^sub>1 = Some y\<close>
        by (auto simp: ran_def)
      then obtain B: \<open>x\<^sub>1 \<in> dom f\<close> \<open>y\<^sub>1 \<in> dom f\<close> by auto
      then obtain C: \<open>x\<^sub>1 \<in> dom (g \<circ>\<^sub>m f)\<close> \<open>y\<^sub>1 \<in> dom (g \<circ>\<^sub>m f)\<close>
        using A
      show \<open>x = y\<close> sorry
    qed

  next
    case (unique_out x)
    then show ?thesis sorry
  qed

    fix x y
    assume A: \<open>x \<in> ran f\<close> \<open>y \<in> ran f\<close> \<open>g x = g y\<close>
    show  \<open>x = y\<close>  sorry
  qed
  show \<open>inj_on (g \<circ>\<^sub>m f) X\<close> if as: \<open>inj_on f X\<close> \<open>inj_on g (ran f)\<close>
  proof
    fix x y
    assume A: \<open>x \<in> X\<close> \<open>y \<in> X\<close> \<open>(g \<circ>\<^sub>m f) x = (g \<circ>\<^sub>m f) y\<close>
    show  \<open>x = y\<close>  sorry
  qed
qed

lemma map_comp_inj_on:
  
  assumes \<open>inj_on f X\<close> \<open>inj_on g Y\<close> \<open>dom g \<subseteq> ran f\<close>
  shows \<open>minj (g \<circ>\<^sub>m f)\<close>
  using assms(3) apply (intro inj_onI ; simp)
proof -
  define h where \<open>h = g \<circ> the \<circ> f\<close>
  have A: \<open>(g \<circ>\<^sub>m f) x = (g \<circ> the \<circ> f) x\<close> if as: \<open>x \<in> dom f\<close> for x
    apply (simp add: map_comp_def)
    apply (cases \<open>f x\<close> ; simp)
    using as by blast
  have \<open>inj_on (g \<circ> the \<circ> f) (dom f)\<close>
    apply (intro comp_inj_on assms)
    oops

end