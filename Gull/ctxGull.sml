
use "flatGull.sml";

datatype sort = intvar |intval |boolvar |boolval | program |unbound | label
fun cmps y (i,x) = (x = y);  (* Usage: findi (cmps id) arr, return SOME (ind,
  "id") if found or NONE if not *)

fun idlook y x = (let val (id,tp)=x in id = y end);

exception chkextendEnvErr;
exception allocateErr;
exception applyEnvErr;
exception chktypeErr;
exception typifyErr
exception checkErr
exception chkelabErr
exception chktypeErr
exception chkelabErr
exception addvarErr


fun emptyEnv() = let val env = nil:(string * sort) list in env end

 and chkextendnEnv(env,ide,sort) = 
  let val v = List.find (idlook ide) env
   in case v of
           SOME (id,v)  => ((ide,sort)::env) 
         | NONE  => ( (ide,sort)::env ) 
   end
   
 and chkextendEnv(env,ide,sort) = 
  let val v = List.find (idlook ide) env
   in case v of
           SOME (id,v)  => (print("variable:"^id^" has been declared!\n");raise
           chkextendEnvErr) 
         | NONE  => ( (ide,sort)::env ) 
   end
   

and chkapplyEnv(locenv,ide)=
  let val ts = List.find (idlook ide) locenv
  in case ts of 
          NONE => (unbound)  (*(print(ide^" is unbound!\n");unbound)*)
        | SOME (id, dv) =>  (dv)
  end

and chktype (ASTTP tp) = 
   if tp = "integer" then intvar
      else if tp = "boolean" then boolvar
         else (print "Unregnized declared type!\n"; raise chktypeErr)

fun validate (PROG (CMDLST(lblst))) =  
let val emptyenv = emptyEnv() 
    val env = chkextendEnv(emptyenv,"1",program)
   in (examine lblst env) end

and addvar(env,nil) = env
   |addvar(env,cmd::lst)=
   case cmd of
   ASGN (ide, exp) => let val tp = (typify exp env) 
                        in if tp=intval then (chkextendEnv(env,ide,intvar))
                           else if tp=boolval then (chkextendEnv(env,ide,boolvar))
                           else (print("Impossible!\n");raise addvarErr)
                         end
   |ASTWHILE ( exp, cmds ) =>  (addvar(env,cmds))
   | ASTIF1 ( exp, cmdst, cmdsf )  =>  (addvar(env,cmdst@cmdsf))
      |_ => env

and chklbs (nil,env) = env
   | chklbs (ASTLABEL(id,cmds)::lblst, env) =
   let val env1 = chkextendEnv(env,id,label)
       val env2 = addvar(env1,cmds)
   in (chklbs (lblst,env2))
   end

and examine (lblst) env = let val env1 = chklbs(lblst,env) 
                              in (checks lblst env1) end


and checks (nil) env = true
| checks (cmd::lst) env = let val b1 = (check cmd env)
                              val b2 = (checks lst env)
                          in (b1 andalso b2)
                          end

and check cmd env =
case cmd of
    ASTSKIP => true
   |ASTGOTO(id) => (chkapplyEnv(env,id)<>unbound)
   |ASGN (ide, exp) => true
   |ASTWHILE ( exp, cmds ) =>  ((typify exp env) = boolval andalso (checks cmds env))
   | ASTIF1 ( exp, cmdst, cmdsf )  => ((typify exp env) = boolval andalso
   (checks cmdst env) andalso (checks cmdsf env))
   | ASTREAD ( ide ) => (chkapplyEnv(env,ide) = intvar) orelse (chkapplyEnv(env,ide) = boolvar)
   | ASTWRITE ( exp ) => ((typify exp env) <>unbound)
   |_ =>(raise checkErr)

and typify exp env =
case exp of
    ASTNUM  ( p ) =>  intval
   | ASTBOOL  ( p ) =>  boolval
   | ASTID (p) => (
               case (chkapplyEnv(env,p)) of
                    intvar => intval
                  |boolvar => boolval
                  | intval => intval
                  | boolval => boolval
                  |program => program
                  |unbound => (print "Variable Unbound!\n";raise typifyErr)
                  )

   | ASTNOT (l) => 
              if ((typify l env) = boolval) then boolval
              else (print "Type doesn't match\n"; raise typifyErr)
   | ASTNEG (l) => 
              if ((typify l env) = intval) then intval
              else (print "Type doesn't match\n"; raise typifyErr)
   | ASTPLUS (l, r) => 
              if ((typify l env) = intval) andalso ((typify r env) = intval) then
                intval
              else (print "Type doesn't match\n"; raise typifyErr)
   | ASTMINUS (l, r) => 
              if ((typify l env) = intval) andalso ((typify r env) = intval) then
                intval
              else (print "Type doesn't match\n"; raise typifyErr)
   | ASTTIMES (l, r) => 
              if ((typify l env) = intval) andalso ((typify r env) = intval) then
                intval
              else (print "Type doesn't match\n"; raise typifyErr)
   | ASTDIV (l, r) => 
              if ((typify l env) = intval) andalso ((typify r env) = intval) then
                intval
              else (print "Type doesn't match\n"; raise typifyErr)
   | ASTAND (l, r) => 
              if ((typify l env) = boolval) andalso ((typify r env) = boolval) then
                boolval
              else (print "Type doesn't match\n"; raise typifyErr)
   | ASTOR (l, r) => 
              if ((typify l env) = boolval) andalso ((typify r env) = boolval) then
                boolval
              else (print "Type doesn't match\n"; raise typifyErr)
   | ASTLESS (l, r) => 
              if ((typify l env) = intval) andalso ((typify r env) = intval) then
                boolval
              else (print "Type doesn't match\n"; raise typifyErr)
   | ASTLESSEQ (l, r) => 
              if ((typify l env) = intval) andalso ((typify r env) = intval) then
                boolval
              else (print "Type doesn't match\n"; raise typifyErr)
   | ASTGRTR (l, r) => 
              if ((typify l env) = intval) andalso ((typify r env) = intval) then
                boolval
              else (print "Type doesn't match\n"; raise typifyErr)
   | ASTGRTREQ (l, r) => 
              if ((typify l env) = intval) andalso ((typify r env) = intval) then
                boolval
              else (print "Type doesn't match\n"; raise typifyErr)
   | ASTEQ (l, r) => 
              if ((typify l env) = intval) andalso ((typify r env) = intval)
              orelse (((typify l env) = boolval) andalso (typify r env =
              boolval)) then
                boolval
              else (print "Type doesn't match\n"; raise typifyErr)
   | ASTNEQ (l, r) => 
              if ((typify l env) = intval) andalso ((typify r env) = intval)
              orelse (((typify l env) = boolval) andalso (typify r env = boolval)) then
                boolval
              else (print "Type doesn't match\n"; raise typifyErr)
     | ASTPAREN ( l )  =>  
              if ((typify l env) = boolval) then boolval
              else if ((typify l env) = intval) then intval
                  else  (print "Type doesn't match\n"; raise typifyErr)

val partr = parse_program(readin("1.gull"));
val flat = go(partr);
val chk = validate(flat);
