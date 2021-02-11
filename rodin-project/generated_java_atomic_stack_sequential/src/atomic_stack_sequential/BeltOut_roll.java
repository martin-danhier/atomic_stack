package atomic_stack_sequential; 

import eventb_prelude.*;
import Util.Utilities;

public class BeltOut_roll{
	/*@ spec_public */ private atomicStackMachine2 machine; // reference to the machine 

	/*@ public normal_behavior
		requires true;
		assignable \everything;
		ensures this.machine == m; */
	public BeltOut_roll(atomicStackMachine2 m) {
		this.machine = m;
	}

	/*@ public normal_behavior
		requires true;
 		assignable \nothing;
		ensures \result <==> !machine.get_beltOut().apply(new Integer(1)).equals(machine.null); */
	public /*@ pure */ boolean guard_BeltOut_roll() {
		return !machine.get_beltOut().apply(new Integer(1)).equals(machine.null);
	}

	/*@ public normal_behavior
		requires guard_BeltOut_roll();
		assignable machine.beltOut, machine.elementOnLift;
		ensures guard_BeltOut_roll() &&  machine.get_beltOut().equals(\old(new BRelation<Integer,Integer>(new Pair<Integer,Integer>(1,machine.get_elementOnLift()),new Pair<Integer,Integer>(2,machine.get_beltOut().apply(1))))) &&  machine.get_elementOnLift() == \old(machine.null); 
	 also
		requires !guard_BeltOut_roll();
		assignable \nothing;
		ensures true; */
	public void run_BeltOut_roll(){
		if(guard_BeltOut_roll()) {
			BRelation<Integer,Integer> beltOut_tmp = machine.get_beltOut();
			Integer elementOnLift_tmp = machine.get_elementOnLift();

			machine.set_beltOut(new BRelation<Integer,Integer>(new Pair<Integer,Integer>(1,elementOnLift_tmp),new Pair<Integer,Integer>(2,beltOut_tmp.apply(1))));
			machine.set_elementOnLift(machine.null);

			System.out.println("BeltOut_roll executed ");
		}
	}

}
