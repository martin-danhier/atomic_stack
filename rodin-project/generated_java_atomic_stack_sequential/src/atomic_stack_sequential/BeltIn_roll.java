package atomic_stack_sequential; 

import eventb_prelude.*;
import Util.Utilities;

public class BeltIn_roll{
	/*@ spec_public */ private atomicStackMachine2 machine; // reference to the machine 

	/*@ public normal_behavior
		requires true;
		assignable \everything;
		ensures this.machine == m; */
	public BeltIn_roll(atomicStackMachine2 m) {
		this.machine = m;
	}

	/*@ public normal_behavior
		requires true;
 		assignable \nothing;
		ensures \result <==> (!machine.get_beltIn().apply(new Integer(1)).equals(machine.null) || !machine.get_beltIn().apply(new Integer(2)).equals(machine.null) && ((!machine.get_beltIn().apply(new Integer(2)).equals(machine.null)) ==> (machine.get_elementLift().equals(new Integer(0))))); */
	public /*@ pure */ boolean guard_BeltIn_roll() {
		return (!machine.get_beltIn().apply(new Integer(1)).equals(machine.null) || !machine.get_beltIn().apply(new Integer(2)).equals(machine.null) && BOOL.implication(!machine.get_beltIn().apply(new Integer(2)).equals(machine.null),machine.get_elementLift().equals(new Integer(0))));
	}

	/*@ public normal_behavior
		requires guard_BeltIn_roll();
		assignable machine.beltIn, machine.elementOnLift;
		ensures guard_BeltIn_roll() &&  machine.get_beltIn().equals(\old(new BRelation<Integer,Integer>(new Pair<Integer,Integer>(1,machine.null),new Pair<Integer,Integer>(2,machine.get_beltIn().apply(1))))) &&  machine.get_elementOnLift() == \old(machine.get_beltIn().apply(2)); 
	 also
		requires !guard_BeltIn_roll();
		assignable \nothing;
		ensures true; */
	public void run_BeltIn_roll(){
		if(guard_BeltIn_roll()) {
			BRelation<Integer,Integer> beltIn_tmp = machine.get_beltIn();
			Integer elementOnLift_tmp = machine.get_elementOnLift();

			machine.set_beltIn(new BRelation<Integer,Integer>(new Pair<Integer,Integer>(1,machine.null),new Pair<Integer,Integer>(2,beltIn_tmp.apply(1))));
			machine.set_elementOnLift(beltIn_tmp.apply(2));

			System.out.println("BeltIn_roll executed ");
		}
	}

}
