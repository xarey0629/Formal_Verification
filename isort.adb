with Sort_Types; use Sort_Types;

package body ISort
   with SPARK_Mode
is

   procedure Insertion_Sort (A : in out Nat_Array) is
      X : Natural;
      J : Index;
   begin
      
      for I in A'First + 1 .. A'Last loop
	 pragma Loop_Invariant (

		-- I = A'First + 1 or else Sorted(A, A'First, I - 1)
		Sorted(A, A'First, I - 1)
		-- (if I in A'First + 2 .. A'Last then Sorted(A, A'First, I - 1))
		
	 ); -- COMPLETE THIS
				
	 X := A (I);
	 J := I;
				
	 loop
	    pragma Loop_Invariant (
			-- Inner Loop Invariant -- 
			-- J in A'First .. I
			A'First <= J and then J <= I and then I in A'First + 1 .. A'Last 
			
			-- and then (J = A'First or else Sorted(A, A'First, J - 1))
			and then Sorted(A, A'First, J - 1)

			-- and then (J = I or else Sorted(A, J + 1, I))
			and then (Sorted(A, J + 1, I))

			and then ((J = A'First or J = I) or else (A(J - 1) <= A(J + 1)))
			
			-- and then (for all K in J .. I => X <= A(K))
			and then (J = I or else X <= A(J + 1))

		); -- COMPLETE THIS
		pragma Assert (J <= I);
		pragma Assert (I in A'Range);
	    exit when J = A'First or else A (J - 1) <= X;

	    A (J) := A (J - 1);
	    J := J - 1;

	 end loop;
	A (J) := X;


    end loop;
   end Insertion_Sort;
   

end ISort;
