program prime is
var num,div : integer;
var done : boolean;
begin
read num
while num>0 do
div := 2; done := false;
while div<= num/2 and not(done) do
done := num = div*(num/div);
div := div+1
end while;
if done then write 0
else write num
end if;
read a
end while;  
end
