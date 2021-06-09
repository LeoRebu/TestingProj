import static org.junit.Assert.*;
import java.util.Calendar;
import org.junit.Test;

public class ReportTest {
	Report highSwarmRisk, medSwarmRisk, lowSwarmRisk, needsSuper1, needsSuper2, highStarveRisk, lowStarveRisk;
	Report bonus;
	
	public ReportTest() {
		Calendar cal = Calendar.getInstance();
		cal.set(2020,0,1);
		highSwarmRisk = new Report(cal.getTime(),10,5,11,true,true,0,0);
		medSwarmRisk = new Report(cal.getTime(),10,5,8,true,true,1,(float)0.5);
		lowSwarmRisk = new Report(cal.getTime(),9,5,10,true,false,0,0);
		needsSuper1 = new Report(cal.getTime(),7,5,8,true,true,1,(float)0.9); 
		needsSuper2 = new Report(cal.getTime(),9,4,10,true,false,0,0); 
		highStarveRisk = new Report(cal.getTime(),11,2,10,true,true,1,(float)0.9); 
		lowStarveRisk = new Report(cal.getTime(),9,4,10,true,false,0,0); 
	}
	
	@Test
	public void testConstructor() {
		assertNotNull(highSwarmRisk);
		assertNotNull(medSwarmRisk);
		assertNotNull(lowSwarmRisk);
		assertNull(bonus);
	}
	
	@Test
	public void testConstruction() {
		Calendar cal = Calendar.getInstance();
		cal.set(2020,0,1);
		Report testRep = new Report();
		int broodFrames = 8;
		
		testRep.setDate(cal.getTime());
		testRep.setBroodFrames(broodFrames);
		testRep.setHoneyFrames(2);
		testRep.setBeeFrames(10);
		testRep.setSeenQueen(false);
		testRep.setSwarmCells(true);
		testRep.setNumSupers(1);
		testRep.setPercTopSuper((float)0.9);
		
		assertEquals(2, testRep.getHoneyFrames());
		assertEquals(10, testRep.getBeeFrames());
		assertEquals(1, testRep.getNumSupers());	
		assertTrue(!testRep.getSeenQueen());	
		assertTrue(testRep.getSwarmCells());
	    assertSame(broodFrames, testRep.getBroodFrames());
		assertTrue(testRep.getPercTopSuper() == 0.9);
	}



	@Test
	public void testSwarm() {
		assertTrue(highSwarmRisk.swarmRisk()==5);
		assertTrue(medSwarmRisk.swarmRisk()==3);
		assertTrue(lowSwarmRisk.swarmRisk()==0);
	}

	@Test
	public void testStarve() {
		assertEquals(5,highStarveRisk.starvingRisk());
		assertEquals(0,lowStarveRisk.starvingRisk());
	}
	
	@Test
	public void testSuper() {
		assertTrue(needsSuper1.needsSuper());
		assertTrue(needsSuper2.needsSuper());
		assertTrue(needsSuper2.needsSuper());
	}
	
	@Test
	public void testSuperPercentage() {
		highSwarmRisk.setPercTopSuper((float)0.5);
		if (highSwarmRisk.getNumSupers() == 0 && highSwarmRisk.getPercTopSuper() > 0)
			fail();
	}
	
	@Test
	public void testSwarmMCDC() {
		Calendar cal = Calendar.getInstance();
		cal.set(2020,0,1);
		Report reportMcdc = new Report(cal.getTime(),3,2,4,true,false,0,0);
		assertEquals(0, reportMcdc.swarmRisk());
		// 4 Possibili condizioni che possono incrementare il rischio di sciamatura
		// Condizione 1: favi di covata >9 (incrementa di 1)
		reportMcdc.setBroodFrames(10);
		assertEquals(1, reportMcdc.swarmRisk());
		// Condizione 2: presenza di celle di sciamatura (incr. 2)
		reportMcdc.setSwarmCells(true);
		assertEquals(3, reportMcdc.swarmRisk());
		// Condizione 3: favi d'api >10 senza melari (incr. 1)
		reportMcdc.setBeeFrames(11);
		assertEquals(3, reportMcdc.swarmRisk());
		reportMcdc.setNumSupers(1);
		assertEquals(4, reportMcdc.swarmRisk());
		
		// Condizione 4.1: favi di miele > 4 con almeno un melario, riempimento <0.8)
		reportMcdc.setHoneyFrames(5);
		assertEquals(4, reportMcdc.swarmRisk());
		// Condizione 4.2: favi di miele > 4 con almeno un melario, riempimento >=0.8)
		reportMcdc.setPercTopSuper((float)0.8);
		assertEquals(5, reportMcdc.swarmRisk());
		// Condizione 4.3: favi di miele > 4 senza melari
		reportMcdc.setNumSupers(0);
		reportMcdc.setPercTopSuper(0);
		assertEquals(5, reportMcdc.swarmRisk());
		
		
	}
}
