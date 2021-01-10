

declare i32 @printf(i8*, ...)

@.str_nl = private constant [2 x i8] c"\0A\00"
@.str_star = private constant [2 x i8] c"*\00"
@.str_space = private constant [2 x i8] c" \00"

define void @new_line() #0 {
  %t0 = getelementptr [2 x i8], [2 x i8]* @.str_nl, i32 0, i32 0
  %1 = call i32 (i8*, ...) @printf(i8* %t0)
  ret void
}

define void @print_star() #0 {
  %t0 = getelementptr [2 x i8], [2 x i8]* @.str_star, i32 0, i32 0
  %1 = call i32 (i8*, ...) @printf(i8* %t0)
  ret void
}

define void @print_space() #0 {
  %t0 = getelementptr [2 x i8], [2 x i8]* @.str_space, i32 0, i32 0
  %1 = call i32 (i8*, ...) @printf(i8* %t0)
  ret void
}

define void @skip() #0 {
  ret void
}

@.str = private constant [4 x i8] c"%d\0A\00"

define void @print_int(i32 %x) {
   %t0 = getelementptr [4 x i8], [4 x i8]* @.str, i32 0, i32 0
   call i32 (i8*, ...) @printf(i8* %t0, i32 %x) 
   ret void
}

; END OF BUILD-IN FUNCTIONS (prelude)
@Ymin = global double -1.3
@Ymax = global double 1.3
@Ystep = global double 0.05
@Xmin = global double -2.1
@Xmax = global double 1.1
@Xstep = global double 0.02
@Maxiters = global i32 1000
define void @m_iter (i32 %m, double %x, double %y, double %zr, double %zi) {
   %tmp_26 = load i32 , i32* @Maxiters
   %tmp_25 = icmp sle i32  %tmp_26, %m
   br i1 %tmp_25, label %if_branch_42, label %else_branch_43

if_branch_42:
   call void @print_star()
   ret void

else_branch_43:
   %tmp_30 = fmul double  %zi, %zi
   %tmp_31 = fmul double  %zr, %zr
   %tmp_29 = fadd double  %tmp_30, %tmp_31
   %tmp_28 = fcmp ole double  4.0, %tmp_29
   br i1 %tmp_28, label %if_branch_44, label %else_branch_45

if_branch_44:
   call void @print_space()
   ret void

else_branch_45:
   %tmp_33 = add i32  %m, 1
   %tmp_36 = fmul double  %zr, %zr
   %tmp_37 = fmul double  %zi, %zi
   %tmp_35 = fsub double  %tmp_36, %tmp_37
   %tmp_34 = fadd double  %x, %tmp_35
   %tmp_40 = fmul double  %zr, %zi
   %tmp_39 = fmul double  2.0, %tmp_40
   %tmp_38 = fadd double  %tmp_39, %y
   call void @m_iter(i32 %tmp_33, double %x, double %y, double %tmp_34, double %tmp_38)
   ret void
}

define void @x_iter (double %x, double %y) {
   %tmp_47 = load double , double* @Xmax
   %tmp_46 = fcmp ole double  %x, %tmp_47
   br i1 %tmp_46, label %if_branch_53, label %else_branch_54

if_branch_53:
   call void @m_iter(i32 0, double %x, double %y, double 0.0, double 0.0)
   %tmp_50 = load double , double* @Xstep
   %tmp_49 = fadd double  %x, %tmp_50
   call void @x_iter(double %tmp_49, double %y)
   ret void

else_branch_54:
   call void @skip()
   ret void
}

define void @y_iter (double %y) {
   %tmp_56 = load double , double* @Ymax
   %tmp_55 = fcmp ole double  %y, %tmp_56
   br i1 %tmp_55, label %if_branch_64, label %else_branch_65

if_branch_64:
   %tmp_57 = load double , double* @Xmin
   call void @x_iter(double %tmp_57, double %y)
   call void @new_line()
   %tmp_61 = load double , double* @Ystep
   %tmp_60 = fadd double  %y, %tmp_61
   call void @y_iter(double %tmp_60)
   ret void

else_branch_65:
   call void @skip()
   ret void
}

define i32 @main() {
   %tmp_66 = load double , double* @Ymin
   call void @y_iter(double %tmp_66)
   ret i32 0
}

