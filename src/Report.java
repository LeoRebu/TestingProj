import java.util.Calendar;
import java.util.Date;

public class Report {
	private Date reportDate; // Identificativo report
	private int broodFrames; // Numero favi con covata (indicativo di crescita) 
	private int honeyFrames; // Numero favi con miele nella cassa (indicativo di richiesta melari)
	private int beeFrames;	// Numero favi con api (indicativo di affollamento)
	private Boolean seenQueen; // Mancanza della regina 
	private Boolean swarmCells; // Presenza cupolino (indicativo di sciamatura)
	private int numSupers; // Numero di melari presenti
	private float percTopSuper; // Percentuale utilizzo ULTIMO melario (tra 0 ed 1)
	
	public Report() {
		Calendar cal = Calendar.getInstance();
		cal.set(2020,0,1);
		reportDate = new Date();
		reportDate = cal.getTime();
		broodFrames=0;
		honeyFrames=0;
		beeFrames=0;
		seenQueen=false;
		swarmCells=false;
		numSupers=0;
		percTopSuper=0;
	}
	
	public Report(Date d, int bf, int hf, int bef, Boolean sq, Boolean sc, int ns, float pts) {
		reportDate = d;
		broodFrames=bf;
		honeyFrames=hf;
		beeFrames=bef;
		seenQueen=sq;
		swarmCells=sc;
		numSupers=ns;
		percTopSuper=pts;
	}
	
	public void setDate(Date d) {
		reportDate = d;
	}
	public void setBroodFrames(int bf) {
		broodFrames = bf;
	}
	public void setHoneyFrames(int hf) {
		honeyFrames = hf;
	}
	public void setBeeFrames(int bef) {
		beeFrames = bef;
	}
	public void setSeenQueen(Boolean sq) {
		seenQueen = sq;
	}
	public void setSwarmCells(Boolean sc) {
		swarmCells = sc;
	}
	public void setNumSupers(int ns) {
		numSupers = ns;
	}
	public void setPercTopSuper(float pts) {
		percTopSuper = pts;
	}
	
	
	public Date getDate() {
		return reportDate;
	}
	public int getBroodFrames() {
		return broodFrames;
	}
	public int getHoneyFrames() {
		return honeyFrames;
	}
	public int getBeeFrames() {
		return beeFrames;
	}
	public Boolean getSeenQueen() {
		return seenQueen;
	}
	public Boolean getSwarmCells() {
		return swarmCells;
	}
	public int getNumSupers() {
		return numSupers;
	}
	public float getPercTopSuper() {
		return percTopSuper;
	}
	
	// Ritorna un valore tra 0 e 5 rappresentante il rischio di sciamatura
	public int swarmRisk() {
		int risk = 0;
		if (broodFrames > 9)
			risk++;
		
		if (swarmCells)
			risk+=2;
		
		if (beeFrames > 10 && numSupers==0)
			risk++;
		
		if (honeyFrames > 4)
			if (numSupers == 0)
				risk++;
			else if (percTopSuper >= 0.8)
				risk++;
				
		
		return risk;
	}
	
	// Ritorna un valore tra 0 e 5 rappresentante il rischio di denutrimento
	public int starvingRisk() {
		int risk = 0;
		if (honeyFrames < 2) {
			risk++;
			if (numSupers == 0)
				risk++;
			else {
				if (beeFrames > 9)
					risk++;
				if (broodFrames > 10)
					risk+=2;
			}
		}
		
		return risk;
	}
	
	//Ritorna un boolean rappresentante la necessità di aggiungere un melario
	public Boolean needsSuper() {
		if ( honeyFrames > 3)
			if (numSupers == 0)
				return true;
			else if (numSupers < 2 && percTopSuper >= 0.8)
				return true;
		
		return false;
	}
}
