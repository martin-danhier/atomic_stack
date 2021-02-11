package atomic_stack_sequential;
import java.util.Random;
import Util.Utilities;
import eventb_prelude.*;

public class Test_atomicStackMachine2{

	public static Integer random_nbElementsPerFloor;
	public static Integer random_null;
	public static Integer random_nbFloors;
	public static Integer random_cadmium;
	public static Integer random_uranium;

	static Random rnd = new Random();
	static Integer max_size_BSet = 10;
	Integer min_integer = Utilities.min_integer;
	Integer max_integer = Utilities.max_integer;

	public Integer GenerateRandomInteger(){
		BSet<Integer> S =  new BSet<Integer>(
				new Enumerated(min_integer, max_integer)
				);
		/** User defined code that reflects axioms and theorems: Begin **/

		/** User defined code that reflects axioms and theorems: End **/

		return (Integer) S.toArray()[rnd.nextInt(S.size())];
	}

	public boolean GenerateRandomBoolean(){
		boolean res = (Boolean) BOOL.instance.toArray()[rnd.nextInt(2)];

		/** User defined code that reflects axioms and theorems: Begin **/

		/** User defined code that reflects axioms and theorems: End **/

		return res;
	}


	public BSet<Integer> GenerateRandomIntegerBSet(){
		int size = rnd.nextInt(max_size_BSet);
		BSet<Integer> S = new BSet<Integer>();
		while (S.size() != size){
			S.add(GenerateRandomInteger());
		}

		/** User defined code that reflects axioms and theorems: Begin **/

		/** User defined code that reflects axioms and theorems: End **/

		return S;
	}

	public BSet<Boolean> GenerateRandomBooleanBSet(){
		int size = rnd.nextInt(2);
		BSet<Boolean> res = new BSet<Boolean>();
		if (size == 0){
			res = new BSet<Boolean>(GenerateRandomBoolean());
		}else{
			res = new BSet<Boolean>(true,false);
		}

		/** User defined code that reflects axioms and theorems: Begin **/

		/** User defined code that reflects axioms and theorems: End **/

		return res;
	}

	public BRelation<Integer,Integer> GenerateRandomBRelation(){
		BRelation<Integer,Integer> res = new BRelation<Integer,Integer>();
		int size = rnd.nextInt(max_size_BSet);
		while (res.size() != size){
			res.add(
					new Pair<Integer, Integer>(GenerateRandomInteger(), GenerateRandomInteger()));
		}
		/** User defined code that reflects axioms and theorems: Begin **/

		/** User defined code that reflects axioms and theorems: End **/

		return res;
	}

	public static void main(String[] args){
		Test_atomicStackMachine2 test = new Test_atomicStackMachine2();

		/** User defined code that reflects axioms and theorems: Begin **/
		test.random_nbElementsPerFloor = test.GenerateRandomInteger();
		test.random_null = test.GenerateRandomInteger();
		test.random_nbFloors = test.GenerateRandomInteger();
		test.random_cadmium = test.GenerateRandomInteger();
		test.random_uranium = test.GenerateRandomInteger();
		/** User defined code that reflects axioms and theorems: End **/

		atomicStackMachine2 machine = new atomicStackMachine2();
		int n = 10; //the number of events in the machine
		//Init values for parameters in event: Bar_new
		Integer element = Utilities.someVal(new BSet<Integer>((new Enumerated(1,Utilities.max_integer))));

		//Init values for parameters in event: Bar_in
		Integer destinationFloor = Utilities.someVal(new BSet<Integer>((new Enumerated(1,Utilities.max_integer))));

		//Init values for parameters in event: Bar_withdraw
		Integer fromFloor = Utilities.someVal(new BSet<Integer>((new Enumerated(1,Utilities.max_integer))));

		while (true){
			switch (rnd.nextInt(n)){
			case 0: if (machine.evt_Lift_up.guard_Lift_up())
				machine.evt_Lift_up.run_Lift_up(); break;
			case 1: if (machine.evt_Lift_down.guard_Lift_down())
				machine.evt_Lift_down.run_Lift_down(); break;
			case 2: if (machine.evt_BeltIn_roll.guard_BeltIn_roll())
				machine.evt_BeltIn_roll.run_BeltIn_roll(); break;
			case 3: if (machine.evt_Send_out.guard_Send_out())
				machine.evt_Send_out.run_Send_out(); break;
			case 4: if (machine.evt_BeltOut_roll.guard_BeltOut_roll())
				machine.evt_BeltOut_roll.run_BeltOut_roll(); break;
			case 5: if (machine.evt_Bar_out.guard_Bar_out())
				machine.evt_Bar_out.run_Bar_out(); break;
			case 6: if (machine.evt_Bar_new.guard_Bar_new(element))
				machine.evt_Bar_new.run_Bar_new(element); break;
			case 7: if (machine.evt_Bar_in.guard_Bar_in(destinationFloor))
				machine.evt_Bar_in.run_Bar_in(destinationFloor); break;
			case 8: if (machine.evt_Bar_insert.guard_Bar_insert())
				machine.evt_Bar_insert.run_Bar_insert(); break;
			case 9: if (machine.evt_Bar_withdraw.guard_Bar_withdraw(fromFloor))
				machine.evt_Bar_withdraw.run_Bar_withdraw(fromFloor); break;
			}
			element = Utilities.someVal(new BSet<Integer>((new Enumerated(1,Utilities.max_integer))));
			destinationFloor = Utilities.someVal(new BSet<Integer>((new Enumerated(1,Utilities.max_integer))));
			fromFloor = Utilities.someVal(new BSet<Integer>((new Enumerated(1,Utilities.max_integer))));
		}
	}

}
