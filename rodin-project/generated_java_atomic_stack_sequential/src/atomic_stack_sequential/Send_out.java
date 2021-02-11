package atomic_stack_sequential; 

import eventb_prelude.*;
import Util.Utilities;

public class Send_out{
	/*@ spec_public */ private atomicStackMachine2 machine; // reference to the machine 

	/*@ public normal_behavior
		requires true;
		assignable \everything;
		ensures this.machine == m; */
	public Send_out(atomicStackMachine2 m) {
		this.machine = m;
	}

	/*@ public normal_behavior
		requires true;
 		assignable \nothing;
		ensures \result <==> (machine.get_elementLift().equals(new Integer(0)) && !machine.get_elementOnLift().equals(machine.null)); */
	public /*@ pure */ boolean guard_Send_out() {
		return (machine.get_elementLift().equals(new Integer(0)) && !machine.get_elementOnLift().equals(machine.null));
	}

	/*@ public normal_behavior
		requires guard_Send_out();
		assignable machine.elementOnLift, machine.beltOut;
		ensures guard_Send_out() &&  machine.get_elementOnLift() == \old(machine.null) &&  machine.get_beltOut().equals(\old((machine.get_beltOut().override(new BRelation<Integer,Integer>(new Pair<Integer,Integer>(1,machine.get_elementOnLift())))))); 
	 also
		requires !guard_Send_out();
		assignable \nothing;
		ensures true; */
	public void run_Send_out(){
		if(guard_Send_out()) {
			Integer elementOnLift_tmp = machine.get_elementOnLift();
			BRelation<Integer,Integer> beltOut_tmp = machine.get_beltOut();

			machine.set_elementOnLift(machine.null);
			machine.set_beltOut((beltOut_tmp.override(new BRelation<Integer,Integer>(new Pair<Integer,Integer>(1,elementOnLift_tmp)))));

			System.out.println("Send_out executed ");
		}
	}

}
