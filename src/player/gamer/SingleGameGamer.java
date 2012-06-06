package player.gamer;

import java.util.ArrayList;
import java.util.List;

import player.event.PlayerTimeEvent;
import player.gamer.event.GamerCompletedMatchEvent;
import player.gamer.event.GamerNewMatchEvent;
import player.gamer.event.GamerUnrecognizedMatchEvent;
import player.gamer.exception.MetaGamingException;
import player.gamer.exception.MoveSelectionException;
import util.game.Game;
import util.gdl.grammar.GdlPool;
import util.gdl.grammar.GdlProposition;
import util.gdl.grammar.GdlSentence;
import util.logging.GamerLogger;
import util.match.Match;
import util.observer.Event;
import util.observer.Observer;
import util.observer.Subject;
import apps.player.config.ConfigPanel;
import apps.player.config.EmptyConfigPanel;
import apps.player.detail.DetailPanel;
import apps.player.detail.EmptyDetailPanel;


public abstract class SingleGameGamer extends Gamer implements Subject{
	
	private Match match;
	private GdlProposition roleName;

	public SingleGameGamer()
	{
		observers = new ArrayList<Observer>();
		
		// When not playing a match, the variables 'match'
		// and 'roleName' should be NULL. This indicates that
		// the player is available for starting a new match.
		match = null;
		roleName = null;
	}

	/* The following values are recommendations to the implementations
	 * for the minimum length of time to leave between the stated timeout
	 * and when you actually return from metaGame and selectMove. They are
	 * stored here so they can be shared amongst all Gamers. */
    public static final long PREFERRED_METAGAME_BUFFER = 3900;
    public static final long PREFERRED_PLAY_BUFFER = 1900;    
	
    protected abstract void metaGame (long timeout) throws MetaGamingException;
    
	// ==== The Gaming Algorithms ====
    @Override
	public boolean start(String matchId, GdlProposition roleName, Game game, 
			int startClock, int playClock, long receptionTime) throws MetaGamingException {
				// Ensure that we aren't already playing a match. If we are,           
        // ignore the message, saying that we're busy.
		if (!ping()) {
	        GamerLogger.logError("GamePlayer", "Got start message while already busy playing a game: ignoring.");
	        notifyObservers(new GamerUnrecognizedMatchEvent(matchId));       
	        return false;
	    }
		
        // Create the new match, and handle all of the associated logistics
        // in the gamer to indicate that we're starting a new match.
		Match match = new Match(matchId, startClock, playClock, game);		
		notifyObservers(new GamerNewMatchEvent(match, roleName));
    	
		this.match = match;
		this.roleName = roleName;
		
		int startClockTimeMillis = match.getStartClock() * 1000;
		notifyObservers(new PlayerTimeEvent(startClockTimeMillis));
		long timeout = receptionTime + getMatch().getStartClock()*1000;
		metaGame (timeout);
		
		return true;
	}
	
	protected abstract GdlSentence selectMove(long timeout) throws MoveSelectionException;
	
	/* Note that the match's goal values will not necessarily be known when
	 * stop() is called, as we only know the final set of moves and haven't
	 * interpreted them yet. To get the final goal values, process the final
	 * moves of the game.
	 */
	protected abstract void stopCleanup(List<GdlSentence> moves);

	protected abstract void abortCleanup();

	public final GdlSentence play(String matchId, List<GdlSentence> moves, long receptionTime) 
			throws MoveSelectionException {

		// First, check to ensure that this play request is for the match
	    // we're currently playing. If we're not playing a match, or we're
	    // playing a different match, send back "busy".
		if (!acceptPlay(matchId)) {
			notifyObservers(new GamerUnrecognizedMatchEvent(matchId));
			GamerLogger.logError("GamePlayer", "Got play message not intended for current game: ignoring.");
			return null;
		}
		
		if (moves != null) {
			getMatch().appendMoves(moves);
		}

    	Match match = getMatch(matchId);
    	if (match != null) notifyObservers(new PlayerTimeEvent(match.getPlayClock() * 1000));
		long timeout = receptionTime + getMatch().getPlayClock()*1000;
		return selectMove(timeout);
	}
	
	public final boolean stop(String matchId, List<GdlSentence> moves) {
		// First, check to ensure that this stop request is for the match
        // we're currently playing. If we're not playing a match, or we're
        // playing a different match, send back "busy".	    
		if (!acceptStop(matchId))
		{
		    GamerLogger.logError("GamePlayer", "Got stop message not intended for current game: ignoring.");
			notifyObservers(new GamerUnrecognizedMatchEvent(matchId));
			return false;
		}
		
		notifyObservers(new GamerCompletedMatchEvent());
		
		//TODO: Add goal values
		if(moves != null) {
			getMatch().appendMoves(moves);
		}		
		getMatch().markCompleted(null);
		
		stopCleanup (moves);
		matchCleanup();
		GdlPool.drainPool();
		return true;
	}
	
	public final boolean abort(String matchId) {
		// First, check to ensure that this abort request is for the match
        // we're currently playing. If we're not playing a match, or we're
        // playing a different match, send back "busy".	    
		if (!acceptAbort(matchId)) 
		{
		    GamerLogger.logError("GamePlayer", "Got abort message not intended for current game: ignoring.");
			notifyObservers(new GamerUnrecognizedMatchEvent(matchId));
			return false;
		}
		abortCleanup();
		matchCleanup();
		notifyObservers(new GamerCompletedMatchEvent());
		return true;
	}

	private void matchCleanup() {
		this.match = null;
		this.roleName = null;
	}
	
	/** 
	 * @return true if the Gamer is ready to receive a start message for a new game
	 */
	public boolean ping() {
		return this.getMatch() == null;		
	}
	
	public void abortAll() {
		if (match != null) {
			this.abort(this.match.getMatchId());
		}
	}
	
	protected boolean matchIdMatch(String matchId) {
		if(getMatch() == null) return false;
		if(!getMatch().getMatchId().equals(matchId)) return false;
		return true;
	}
	
	public boolean acceptPlay(String matchId) {
		boolean accept = matchIdMatch(matchId);
		return accept;
	}
	
	public boolean acceptStop(String matchId) {
		return matchIdMatch(matchId);
	}
	
	public boolean acceptAbort(String matchId) {
		boolean accept =  matchIdMatch(matchId);
		return accept;
	}
	
	// ==== Gamer Profile and Configuration ====
	public String getName() {
		return this.getClass().getName();
	}
	
	public ConfigPanel getConfigPanel() {
		return new EmptyConfigPanel();
	}
	
	public DetailPanel getDetailPanel() {
		return new EmptyDetailPanel();
	}

	// ==== Accessors ====	
	/**
	 * @return the match the Gamer is currently playing
	 */
	public final Match getMatch() {
		return match;
	}
	
	public final GdlProposition getRoleName() {
		return roleName;
	}
	
	public Match getMatch(String matchId) {
		if (this.match != null && matchId.equals(this.match.getMatchId())) return this.match;
		return null;
	}
	
	// ==== Observer Stuff ====
	private final List<Observer> observers;
	public final void addObserver(Observer observer)
	{
		observers.add(observer);
	}
	
	public final void notifyObservers(Event event)
	{
		for (Observer observer : observers) {
			observer.observe(event);
		}
	}

}