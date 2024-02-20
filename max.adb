package body Max 
   with SPARK_Mode  
is

   function Arrays_Max (A : in Our_Array) return Index_Range is
      X : Index_Range := Index_Range'First;
      Y : Index_Range := Index_Range'Last;
   begin
      while X /= Y loop
         pragma Loop_Invariant (
            (for all K in Index_Range'First .. X => A(K) <= Content_Range'Max(A(X), A(Y))) -- *** Question here ***
            and then (for all Q in Y .. Index_Range'Last => A(Q) <= Content_Range'Max(A(X), A(Y)))
            -- and then Index_Range'First <= X and then X < Index_Range'Last
            -- and then Index_Range'First < Y and then Y <= Index_Range'Last
            and then (X < Y)
            ); -- COMPLETE THIS
         pragma Loop_Variant (Decreases => Y - X); -- COMPLETE THIS

         if A (X) <= A (Y) then
            X := X + 1;
         else
            Y := Y - 1;
         end if;
      end loop;
      return X;
   end Arrays_Max;

end Max;
