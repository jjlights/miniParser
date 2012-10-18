program prog1 is
var x,y: integer;
var b,c: boolean;
begin
read x read y write x+y
b := x < y;
if x = y
then c := x <= y;
else c := x > y; end if;
while c do x := x + 1 end while;
b := b and (b or c);
end
