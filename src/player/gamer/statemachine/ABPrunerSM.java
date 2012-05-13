package player.gamer.statemachine;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;

import util.statemachine.MachineState;
import util.statemachine.Move;
import util.statemachine.Role;
import util.statemachine.StateMachine;
import util.statemachine.exceptions.GoalDefinitionException;
import util.statemachine.exceptions.MoveDefinitionException;
import util.statemachine.exceptions.TransitionDefinitionException;
import util.statemachine.implementation.prover.ProverStateMachine;

public class ABPrunerSM extends StateMachineGamer {
	
	private static final int MAX_SCORE = 100;

	private List<Role> _opp_roles;
	private HashMap<MachineState,Integer> _cache;
	
	private class Move_Node {
		public int value;
		public Move move;
		public Move_Node(int value, Move move){
			this.value = value;
			this.move = move;
		}
	}
	
	@Override
	public StateMachine getInitialStateMachine() {	
		return new ProverStateMachine();
	}

	@Override
	public void stateMachineAbort() {
		// TODO Auto-generated method stub

	}

	@Override
	public void stateMachineMetaGame(long timeout)
			throws TransitionDefinitionException, MoveDefinitionException,
			GoalDefinitionException {
		_opp_roles = new ArrayList<Role>();
		_cache = new HashMap<MachineState,Integer>();
		ArrayList<Role> all_roles = (ArrayList<Role>) getStateMachine().getRoles();
		for(int i=0; i<all_roles.size(); i++){
			if(!(getRole().equals(all_roles.get(i)))){
				_opp_roles.add(all_roles.get(i));
			}
		}

	}

	@Override
	public Move stateMachineSelectMove(long timeout)
			throws TransitionDefinitionException, MoveDefinitionException,
			GoalDefinitionException {
		List<Move> legalMoves = getStateMachine().getLegalMoves(getCurrentState(), getRole());
		if(legalMoves.size()==1){
			return(legalMoves.get(0));
		}
		return(getValue(getCurrentState(), MAX_SCORE)).move;
	}
	
	private int getOppWorstValue(MachineState currState, List<List<Move>> jointMoves, int highestValueSeen) throws TransitionDefinitionException, GoalDefinitionException, MoveDefinitionException {
		int worstValue = MAX_SCORE;
		for(int j=0; j<jointMoves.size(); j++){
			MachineState tempState = getStateMachine().getNextState(currState, jointMoves.get(j));
			int currvalue;
			if(getStateMachine().isTerminal(tempState)){
				currvalue = getStateMachine().getGoal(tempState, getRole());
			} else if(_cache.containsKey(tempState)){
				currvalue = _cache.get(tempState);
			} else {
				currvalue = getValue(tempState, worstValue).value;
				_cache.put(tempState, currvalue);
			}
			//if this move is worse than any previous move, opp will take it, so player doesn't care about this move
			if (currvalue <= highestValueSeen) {
				return 0;
			}
			if(currvalue<worstValue) {
				worstValue = currvalue;
			}
		}
		return worstValue;
	}

	private Move_Node getValue(MachineState currState, int lowestValueSeen) throws MoveDefinitionException, TransitionDefinitionException, GoalDefinitionException{
		Move_Node bestMove = new Move_Node(0,null);
		List<Move> legalMoves = getStateMachine().getLegalMoves(currState, getRole());
		int highestValueSeen = 0;
		for(int i=0; i<legalMoves.size(); i++){
			List<List<Move> > jointMoves = getStateMachine().getLegalJointMoves(currState, getRole(), legalMoves.get(i));
			int oppWorstValue = getOppWorstValue(currState, jointMoves, highestValueSeen);
			if(oppWorstValue > bestMove.value) {
				highestValueSeen = oppWorstValue;
				bestMove.value = oppWorstValue;
				bestMove.move = legalMoves.get(i);
			}
			//If current best move seen by player is better than the lowest value seen, opp will take lower value, so opp will not care about player's choices
			if (bestMove.value >= lowestValueSeen) {
				break;
			}
		}
		return bestMove;			
	}

	@Override
	public void stateMachineStop() {
		// TODO Auto-generated method stub

	}

}
