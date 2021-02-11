package atomic_stack_sequential; 

import eventb_prelude.*;
import Util.Utilities;

public class Lift_up{
	/*@ spec_public */ private atomicStackMachine2 machine; // reference to the machine 

	/*@ public normal_behavior
		requires true;
		assignable \everything;
		ensures this.machine == m; */
	public Lift_up(atomicStackMachine2 m) {
		this.machine = m;
	}

	/*@ public normal_behavior
		requires true;
 		assignable \nothing;
		ensures \result <==> ((machine.get_elementLift()).compareTo(machine.nbFloors) < 0 && machine.get_barTo().equals(new Integer(0))); */
	public /*@ pure */ boolean guard_Lift_up() {
		return ((machine.get_elementLift()).compareTo(machine.nbFloors) < 0 && machine.get_barTo().equals(new Integer(0)));
	}

	/*@ public normal_behavior
		requires guard_Lift_up();
		assignable machine.elementLift;
		ensures guard_Lift_up() &&  machine.get_elementLift() == \old(new Integer(machine.get_elementLift() + 1)); 
	 also
		requires !guard_Lift_up();
		assignable \nothing;
		ensures true; */
	public void run_Lift_up(){
		if(guard_Lift_up()) {
			Integer elementLift_tmp = machine.get_elementLift();

			machine.set_elementLift(new Integer(elementLift_tmp + 1));

			System.out.println("Lift_up executed ");
		}
	}

}
