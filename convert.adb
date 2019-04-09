--
-- A program for converting between various integer representations.
--
-- Supports input as decimal, hex (prefix: 0x), octal (0c), and binary (0b).
-- If the input is large enough to have a word-length highest order bit,
-- it could in theory be a negative number with a *s-compliment repesentation.
-- Hence, those interpretations of the value are shown and differ when natural.
-- Additionally, an optional sign character is supported before every literal.
-- Note that hexadecimal literals mustn't contain lowercase characters.
--
-- This program is hereby placed in the public domain.
--
-- If you live in a country which does not regcognize the above commission,
-- you may wish to instead use this program under a liberal license, below:
--
-- Alternatively, this program is licensed to you under the following terms:
--
-- Copyright (C) 2019, Daniel C.
--
-- Permission to use, copy, modify, and/or distribute this software for
-- any purpose with or without fee is hereby granted.
--
-- THE SOFTWARE IS PROVIDED "AS IS" AND THE AUTHOR DISCLAIMS ALL WARRANTIES
-- WITH REGARD TO THIS SOFTWARE INCLUDING ALL IMPLIED WARRANTIES OF
-- MERCHANTABILITY AND FITNESS. IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR ANY
-- SPECIAL, DIRECT, INDIRECT, OR CONSEQUENTIAL DAMAGES OR ANY DAMAGES WHATSOEVER
-- RESULTING FROM LOSS OF USE, DATA OR PROFITS, WHETHER IN AN ACTION OF
-- CONTRACT, NEGLIGENCE OR OTHER TORTIOUS ACTION, ARISING OUT OF OR IN
-- CONNECTION WITH THE USE OR PERFORMANCE OF THIS SOFTWARE.
--

with Interfaces; use Interfaces;
with Ada.Text_IO;

procedure Convert is
   type    Bit_Pattern is new Unsigned_64;
   type    Signed_Bits is new  Integer_64;
   subtype Numerals    is Bit_Pattern range 0 .. 15; -- Supported digits.
   subtype Num_Base    is Bit_Pattern range 2 .. 16; -- Supported bases.
   subtype Bit_StrLen  is Natural     range 0 .. 66; -- 64 bits + 2 prefix
   subtype Bit_StrIdx  is Positive    range 1 .. 66;
   subtype Bit_String  is String (Bit_StrIdx);

   procedure Print_As_Base (Out_Buf : out Bit_String;
                            End_Idx : out Bit_StrLen;
                            Numeral : in  Bit_Pattern;
                            Base    : in  Num_Base) is
      procedure Rev_String (Input : in out String) is
         E : Positive;  -- Index from end.
         T : Character; -- Temporary char.
      begin
         for I in Input (Input'First .. (Input'First + Input'Last)/2)'Range loop
            E         := Input'Last - I + Input'First; -- Calculate end index --
            T         := Input (I);                    -- Perform simple swap --
            Input (I) := Input (E);
            Input (E) := T;
         end loop;
      end Rev_String;

      procedure Format_Val (Out_Buf : out String;
                            End_Idx : out Bit_StrLen;
                            Numeral : in  Bit_Pattern;
                            Base    : in  Num_Base) is
         Chars_Table : constant array (Numerals) of Character :=
           (0  => '0', 1 => '1', 2 => '2', 3 => '3', 4 => '4',
            5  => '5', 6 => '6', 7 => '7', 8 => '8', 9 => '9',
           10  => 'A',11 => 'B',12 => 'C',13 => 'D',14 => 'E',15 => 'F');
         Decumulator : Bit_Pattern := Numeral;
         Low_Ord_Val : Numerals;
         I           : Positive range 1 .. Bit_StrIdx'Last+1 := Out_Buf'First;
      begin
		 -- Loops at least once, for the case that the input was 0.
         while Decumulator /= 0 or I = Out_Buf'First loop
            Low_Ord_Val := Numerals(Decumulator mod Base);
            Decumulator :=          Decumulator  /  Base;
            Out_Buf (I) := Chars_Table (Low_Ord_Val);

            I := I + 1;
         end loop;
         End_Idx := I - 1;
         Rev_String (Out_Buf (Out_Buf'First .. End_Idx));
      end Format_Val;

      Offset : Bit_StrLen := 0;
   begin
      case Base is -- Write appropriate prefix.
         when 2  =>
            Out_Buf (1 .. 2) := "0b";
            Offset := 2;
         when 8  =>
            Out_Buf (1 .. 2) := "0c";
            Offset := 2;
         when 16 =>
            Out_Buf (1 .. 2) := "0x";
            Offset := 2;
         when others => null;
      end case;

	  -- Write value.
      Format_Val (Out_Buf (Offset+1 .. Out_Buf'Last), End_Idx, Numeral, Base);
   end Print_As_Base;

   procedure Parse_As_Base (Numeral : in  String;
                            Base    : in  Num_Base;
                            Parsed  : out Bit_Pattern;
                            Error   : out Boolean) is
      Accumulator : Bit_Pattern := 0;
      Numeric_Val : Bit_Pattern;
      Value_Table : constant array (Character) of Bit_Pattern :=
        ('0' => 0, '1' => 1, '2' => 2, '3' => 3, '4' => 4,
         '5' => 5, '6' => 6, '7' => 7, '8' => 8, '9' => 9,
         'A' =>10, 'B' =>11 ,'C' =>12, 'D' =>13, 'E' => 14, 'F' => 15,
         others => Bit_Pattern'Last);
   begin
      for Ch of Numeral loop
         Numeric_Val := Value_Table (Ch);
         if Numeric_Val >= Base then
            Error := True;
            return;
         end if;

         Accumulator := Accumulator * Base;
         Accumulator := Accumulator + Numeric_Val;
      end loop;
      Error  := False;
      Parsed := Accumulator;
   end Parse_As_Base;


   procedure Parse_Literal (Literal : in  String;
                            Parsed  : out Bit_Pattern;
                            Error   : out Boolean) is

      Prefix:constant String := (if   Literal'Length > 2
                                 then Literal (Literal'First .. Literal'First+1)
                                 else "");

      Remain:constant String := (if   Literal'Length > 2
                                 then Literal (Literal'First+2 .. Literal'Last)
                                 else "");
   begin
      if    Prefix = "0b" then Parse_As_Base (Remain,  2, Parsed, Error);
      elsif Prefix = "0c" then Parse_As_Base (Remain,  8, Parsed, Error);
      elsif Prefix = "0x" then Parse_As_Base (Remain, 16, Parsed, Error);
      else                     Parse_As_Base (Literal,10, Parsed, Error);
      end if;
   end Parse_Literal;

   -- Parses a literal with an optional sign.
   procedure Parse_SignedL (Literal : in  String;
							Parsed  : out Bit_Pattern;
							Error   : out Boolean) is
	  V : Bit_Pattern := 0;
   begin
	  if Literal (Literal'First) in '-' | '+'
	  then Parse_Literal (Literal (Literal'First+1 .. Literal'Last), V, Error);
	  else Parse_Literal (Literal, V, Error);
	  end if;

	  Parsed := V * (if Literal (Literal'First) = '-' then (-1) else (+1));
   end Parse_SignedL;

   ---------------
   -- MAIN BODY --
   ---------------

   Literal   : Bit_String;
   End_Idx   : Natural;
   Fmt_Error : Boolean;
   Bit_Value : Bit_Pattern;
   Formatted : Bit_String;

	   -- Next power of two that exists as a possible word size. --
	   function Next_Word_Width (Bit_Vect: in Bit_Pattern) return Positive is
		  (if   Bit_Vect >= 2**32 then 64
		  elsif Bit_Vect >= 2**16 then 32
		  elsif Bit_Vect >= 2** 8 then 16
		  else                          8);

	   function Twos_Complement (Unsigned: in Bit_Pattern) return Signed_Bits is
		  H_O_B  :constant Bit_Pattern := +(2**(Next_Word_Width(Unsigned) -1));
		  Is_Set :constant Boolean     :=  (Unsigned >= H_O_B); -- Is HOB set?
		  Weight :constant Signed_Bits := -(Signed_Bits(H_O_B-1))-1;
	   begin return
		 (if Is_Set
			then Signed_Bits(Unsigned - H_O_B) + Weight
			else Signed_Bits(Unsigned));
	   end Twos_Complement;

       function Ones_Complement (Unsigned: in Bit_Pattern) return Signed_Bits is
		  TWC :constant Signed_Bits := Twos_Complement (Unsigned);
	   begin return (if TWC < 0 then TWC+1 else TWC); end;

begin

   Ada.Text_IO.Put_Line ("Provide a numeric value to convert.");
   Ada.Text_IO.Get_Line (Literal, End_Idx);

   Parse_SignedL (Literal (1 .. End_Idx), Bit_Value, Fmt_Error);
   if (Fmt_Error) then
      Ada.Text_IO.Put_Line ("Improperly formatted literal!");
      return;
   end if;

   -- Output --

   Print_As_Base (Formatted, End_Idx, Bit_Value, 2);
   Ada.Text_IO.Put_Line("Bin: "& String(Formatted (1 .. End_Idx)));

   Print_As_Base (Formatted, End_Idx, Bit_Value, 16);
   Ada.Text_IO.Put_Line("Hex: "& String(Formatted (1 .. End_Idx)));

   Print_As_Base (Formatted, End_Idx, Bit_Value, 8);
   Ada.Text_IO.Put_Line("Oct: "& String(Formatted (1 .. End_Idx)));

   Print_As_Base (Formatted, End_Idx, Bit_Value, 10);
   Ada.Text_IO.Put_Line("Dec: "& String(Formatted (1 .. End_Idx)));

   Ada.Text_IO.Put_Line("TsC: "& Signed_Bits'Image(Twos_Complement(Bit_Value)));
   Ada.Text_IO.Put_Line("OsC: "& Signed_Bits'Image(Ones_Complement(Bit_Value)));

end Convert;
