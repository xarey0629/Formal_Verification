with Ada.Text_IO; use Ada.Text_IO;

procedure Array_Example is
   A : array (1 .. 5) of Integer;

begin
   Put_Line("A'First = " & Integer'Image(A'First));
   Put_Line("A'Last  = " & Integer'Image(A'Last));
end Array_Example;