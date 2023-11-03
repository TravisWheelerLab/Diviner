#!/usr/bin/env perl
use warnings;
use strict;
use POSIX;
use Cwd;
use Getopt::Long;
use Time::HiRes;

# I AM UNAVOIDABLE
sub GetScriptDir { return '.' if ($0 !~ /\//); $0 =~ /^(.+)\/[^\/]+$/; return $1; }
use lib GetScriptDir();
use Bureaucracy;
use DisplayProgress;

# Subroutines
sub PrintUsage;
sub DetailedUsage;
sub ParseArgs;
sub GetMappedSeqMSA;
sub ParseAFA;
sub RecordSplicedMSA;
sub RecordSplicedMap;
sub ReduceMSAToSpecies;
sub FindGhostExons;
sub FindAliQualityDrops;
sub RecordGhostMSAs;
sub GatherBestLocalAlis;
sub RangesOverlap;
sub LocalAlign;
sub GetB62Score;
sub MultiAminoSeqAli;
sub GetMapSummaryStats;
sub CollapseAndCountOverlaps;
sub CheckNovelty;
sub RecordNovelty;
sub RecordHitsByPctID;


# Blosum-62 stuff
my @Blosum62
    = ( 4,  0, -2, -1, -2,  0, -2, -1, -1, -1, -1, -1, -1, -1, -1,  1, -1, -2, -3, -2,  0,
	0,  9, -3, -4, -2, -3, -3, -1, -3, -1, -1, -3, -3, -3, -3, -1, -1, -1, -2, -2,  0,
       -2, -3,  6,  2, -3, -1, -1, -3, -1, -4, -3,  1, -1,  0, -2,  0,  1, -3, -4, -3,  0,
       -1, -4,  2,  5, -3, -2,  0, -3,  1, -3, -2,  0, -1,  2,  0,  0,  0, -3, -3, -2,  0,
       -2, -2, -3, -3,  6, -3, -1,  0, -3,  0,  0, -3, -4, -3, -3, -2, -2, -1,  1,  3,  0,
        0, -3, -1, -2, -3,  6, -2, -4, -2, -4, -3, -2, -2, -2, -2,  0,  1,  0, -2, -3,  0,
       -2, -3,  1,  0, -1, -2,  8, -3, -1, -3, -2,  1, -2,  0,  0, -1,  0, -2, -2,  2,  0,
       -1, -1, -3, -3,  0, -4, -3,  4, -3,  2,  1, -3, -3, -3, -3, -2, -2,  1, -3, -1,  0,
       -1, -3, -1,  1, -3, -2, -1, -3,  5, -2, -1,  0, -1,  1,  2,  0,  0, -3, -3, -2,  0,
       -1, -1, -4, -3,  0, -4, -3,  2, -2,  4,  2, -3, -3, -2, -2, -2, -2,  3, -2, -1,  0,
       -1, -1, -3, -2,  0, -3, -2,  1, -1,  2,  5, -2, -2,  0, -1, -1, -1, -2, -1, -1,  0,
       -2, -3,  1,  0, -3,  0, -1, -3,  0, -3, -2,  6, -2,  0,  0,  1,  0, -3, -4, -2,  0,
       -1, -3, -1, -1, -4, -2, -2, -3, -1, -3, -2, -1,  7, -1, -2, -1,  1, -2, -4, -3,  0,
       -1, -3,  0,  2, -3, -2,  0, -3,  1, -2,  0,  0, -1,  5,  1,  0,  0, -2, -2, -1,  0,
       -1, -3, -2,  0, -3, -2,  0, -3,  2, -2, -1,  0, -2,  1,  5, -1, -1, -3, -3, -2,  0,
	1, -1,  0,  0, -2,  0, -1, -2,  0, -2, -1,  1, -1,  0, -1,  4,  1, -2, -3, -2,  0,
       -1, -1,  1,  0, -2,  1,  0, -2,  0, -2, -1,  0,  1,  0, -1,  1,  4, -2, -3, -2,  0,
	0, -1, -3, -2, -1, -3, -3,  3, -2,  1,  1, -3, -2, -2, -3, -2, -2,  4, -3, -1,  0,
       -3, -2, -4, -3,  1, -2, -2, -3, -3, -2, -1, -4, -4, -2, -3, -3, -3, -3, 11,  2,  0,
       -2, -2, -3, -2,  3, -3,  2, -1, -2, -1, -1, -2, -3, -1, -2, -2, -2, -1,  2,  7,  0,
	0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0);

my %AminoIndex
    = ('A', 0,'C', 1,'D', 2,'E', 3,'F', 4,'G', 5,'H', 6,'I', 7,'K', 8,'L', 9,
       'M',10,'N',11,'P',12,'Q',13,'R',14,'S',15,'T',16,'V',17,'W',18,'Y',19,'X',20);
    
my $b62_gap = -4;




##############
#            #
#   SCRIPT   #
#            #
##############



if (@ARGV < 2) {
    if (@ARGV == 1 && lc($ARGV[0]) =~ /\-help/) {
	DetailedUsage();
    }
    PrintUsage();
}


# Figure out what the location of the Mirage src directory is
my $location = $0;
$location =~ s/Diviner\.pl$//;


# Parse any commandline arguments
my $options_ref = ParseArgs();
my %Options = %{$options_ref};
my $num_cpus = $Options{cpus};
my $save_msas = $Options{savemsas}; # Do we want to write our spliced MSAs to files?
my $score_density_threshold = $Options{density};
my $bad_ali_cutoff = $Options{alicutoff};


# Find all the friends we're going to need inside Diviner
my $dependencies_ref = FindDependencies();
my %Dependencies = %{$dependencies_ref};


# We're going to need these friends
my $sindex  = $Dependencies{'sindex'};
my $sfetch  = $Dependencies{'sfetch'};
my $sstat   = $Dependencies{'sstat'};
my $tblastn = $Dependencies{'tblastn'};


# An astute observer will notice that these aren't the same settings as Quilter
# uses, which is because this isn't frickin' Quilter, geez.
# It's rad that our standardized filenames let us play like this!
$tblastn = $tblastn.' -outfmt 6 ';


# Confirm that the input directory looks like the real deal
my $input_dirname = ConfirmDirectory($ARGV[0]);
my $final_results_dirname = ConfirmDirectory($input_dirname.'Final-MSAs');
my $all_species_dirname = ConfirmDirectory($input_dirname.'Species-MSAs');


# Start off the real work by parsing the species guide, which will give
# us genome locations and chromosome lengths.
my $tildedir_check = OpenSystemCommand('echo ~');
my $tildedir = <$tildedir_check>;
$tildedir =~ s/\n|\r//g;
$tildedir = ConfirmDirectory($tildedir);
close($tildedir_check);


# Let the user know that we're getting to work
ReportProgress('startup');


my $SpeciesGuide = OpenInputFile($ARGV[1]);
my %SpeciesToGenomes;
my %SpeciesToGTF;
my %ChrLensBySpecies;
while (my $line = <$SpeciesGuide>) {

    $line =~ s/\n|\r//g;
    next if ($line !~ /(\S+)\s+(\S+)\s+(\S+)/);
    my $species = lc($1);
    my $genome = $2;
    my $gtf = $3;
    $genome =~ s/\~\//$tildedir/;
    $gtf =~ s/\~\//$tildedir/;

    $SpeciesToGenomes{$species} = $genome;

    # I don't know why we'd be at this point, where we have
    # Mirage results without a genome index, but just in case...
    if (!(-e $genome.'.hsi')) {
	print "\n";
	print "  Warning: Couldn't find existing 'hsi' index for genome file '$genome'\n";
	print "           Index creation may take a couple of seconds\n\n";
	RunSystemCommand($sindex.' '.$genome);
	print "  Indexing successful!\n\n";
    }

    # Get chromosome lengths for the genome
    my $SstatOut = OpenSystemCommand($sstat.' '.$genome);
    while (my $sstat_line = <$SstatOut>) {
	$sstat_line =~ s/\n|\r//g;
	if ($sstat_line =~ /^\: (\S+)\s+(\d+)/) {
	    my $chr = $1;
	    my $len = $2;
	    $ChrLensBySpecies{$species.'|'.$chr} = $len;
	}
    }
    close ($SstatOut);

    # We'll read in the species' GTF info so we can determine whether
    # any ghost exons we hit on are known coding regions (and not just
    # members of proteoforms that are missing from our database).
    if (-e $gtf) {
	$SpeciesToGTF{$species} = $gtf;
	#ParseGTF($species,$gtf);
    }
    
}
close($SpeciesGuide);


# As a bit of a sanity-check, if we don't have any genomes then we bail
if (scalar(keys %SpeciesToGenomes) == 0) {
    die "\n  ERROR:  Failed to locate usable genome mappings in species guide file '$ARGV[1]'\n\n";
}


# We'll do a preliminary run through 'FinalMSAs' to compute the total number of
# genes, so that we can figure out how to allocate work for each of our processes.
my $FinalMSAs = OpenDirectory($final_results_dirname);
my @GeneList;
while (my $fname = readdir($FinalMSAs)) {
    next if ($fname !~ /(\S+)\.afa$/);
    push(@GeneList,$1);
}
closedir($FinalMSAs);


# Quick sanity check
if (scalar(@GeneList) == 0) {
    die "\n  ERROR:  No MSA files were found in '$final_results_dirname'...?\n\n";
}


# Are we asking for too many cpus?
$num_cpus = Min($num_cpus,scalar(@GeneList));


# Now that we know that we have solid inputs, we'll create the output directory
my $outdirname  = CreateDirectory($Options{outdirname});
my $outgenesdir = CreateDirectory($outdirname.'Results-by-Gene');
my $bedfilesdir = CreateDirectory($outdirname.'BED-Files');


# Things are looking good if we've made it this far without complaint,
# so let's provide a smidgen of feedback
InitProgressVars($outdirname.'.progress',$num_cpus,scalar(@GeneList));


# Look away, children, the processes are spawning!
my $threadID = SpawnProcesses($num_cpus);


# I've been borned! What's my job?
my $thread_portion = int(scalar(@GeneList)/$num_cpus);
my $start_gene_id = $threadID * $thread_portion;
my $end_gene_id = (1+$threadID) * $thread_portion;
$end_gene_id = scalar(@GeneList) if ($threadID == $num_cpus-1);


# Name temporary filenames that we'll want to use (and, while we're at it,
# fill in all of the wild 'n' wacky tblastn arguments we'll be using).
my $nucl_seq_fname = $outgenesdir.'nucl.tmp'.$threadID.'.fa';
my $prot_seq_fname = $outgenesdir.'prot.tmp'.$threadID.'.fa';
my $tbn_out_fname  = $outgenesdir.'tbn.tmp'.$threadID.'.out';
$tblastn = $tblastn.' -subject '.$nucl_seq_fname.' -query '.$prot_seq_fname;
$tblastn = $tblastn.' -out '.$tbn_out_fname.' 1>/dev/null 2>&1';


# These are going to be what we use to capture whether a hit is novel
# (and trace that info. back to the corresponding file)
my %SpeciesChrMbRangeToHits;
my @ThreadHitNumToFileAndData;
my @ThreadHitNumToNovelty;
my $num_thread_hits = 0;


# TIME FOR THE MAIN EVENT!
#
# We'll do this the easiest (laziest) way, which will just be running
# through each of our final MSAs, loading in *only* those sequences
# which have mappings, and then reverse-engineering exon markers.
#
# Fun!
#
my $total_ghost_exons = 0;
my $total_ghosts_busted = 0;
my @GhostlyGenes;
for (my $gene_id=$start_gene_id; $gene_id<$end_gene_id; $gene_id++) {

    my $completed_genes = $gene_id - $start_gene_id;
    ReportProgress('main-loop|'.$threadID.'|'.$completed_genes);

    my $gene  = $GeneList[$gene_id];
    my $fname = $final_results_dirname.$gene.'.afa';

    # Pull in an MSA that's been (1) reduced to mapped sequences, and
    # (2) has splice site markers.
    my ($msa_ref,$mapmsa_ref,$seqnames_ref,$num_seqs,$msa_len,$speciestochrs_ref)
	= GetMappedSeqMSA($fname,$gene);

    # If we don't have anything to do with this family, skip to the next
    next if (!$msa_ref);
    
    my @MSA = @{$msa_ref};
    my @MapMSA = @{$mapmsa_ref};
    my @SeqNames = @{$seqnames_ref};
    my %SpeciesToChrs = %{$speciestochrs_ref};

    # At this point, it makes sense to create the result directory for this gene
    my $gene_outdir = CreateDirectory($outgenesdir.$gene);

    # Get your butt into this file, mister!
    RecordSplicedMSA(\@MSA,\@SeqNames,$num_seqs,$msa_len,$gene_outdir.'mapped-seqs.afa');

    # Now we'll reduce our MSA even further, down to just one sequence per
    # species!
    ($msa_ref,$mapmsa_ref,$seqnames_ref,$num_seqs)
	= ReduceMSAToSpecies(\@MSA,\@MapMSA,\@SeqNames,$num_seqs,$msa_len);
    @MSA = @{$msa_ref};
    @MapMSA = @{$mapmsa_ref};
    my @SpeciesNames = @{$seqnames_ref};
    my $num_species = $num_seqs;

    # Write these ones out, too!
    RecordSplicedMSA(\@MSA,\@SpeciesNames,$num_seqs,$msa_len,$gene_outdir.'species.afa');
    RecordSplicedMap(\@MSA,\@MapMSA,\@SpeciesNames,\%SpeciesToChrs,$num_seqs,$msa_len,$gene_outdir.'genome-mappings.out');
    
    # Now that we have our super-reduced splice-site-ified MSA, let's get real nasty
    # with it (by way of locating exons suggestive of "ghosts")!
    my ($num_ghost_exons, $num_ghosts_busted) =
	FindGhostExons($gene,\@MSA,\@MapMSA,\@SpeciesNames,$num_species,$msa_len,\%SpeciesToChrs);

    # Add onto our overarching tallies
    $total_ghost_exons += $num_ghost_exons;
    $total_ghosts_busted += $num_ghosts_busted;

    # If we didn't bust any ghosts, then there aren't any MSAs to build or
    # GTFs to examine... yay?
    next if (!$num_ghosts_busted);

    # Time to build some gorgeous translated MSAs!
    RecordGhostMSAs($gene);

    # Eeek! Ghosts!
    push(@GhostlyGenes,$gene);

}


# Figure out which of our hits don't overlap with an 'exon' or 'cds' GTF entry
foreach my $species (keys %SpeciesToGTF) {
    CheckNovelty($species,$SpeciesToGTF{$species});
}
RecordNovelty();


# How'd I do?  I don't even know!
if ($threadID) {
    my $final_outf = OpenOutputFile($outgenesdir.$threadID.'.final-tally.out');
    print $final_outf "$total_ghosts_busted / $total_ghost_exons\n";
    for (my $i=0; $i<scalar(@GhostlyGenes); $i++) {
	print $final_outf '|' if ($i);
	print $final_outf "$GhostlyGenes[$i]";
    }
    print $final_outf "\n";
    close($final_outf);
}


# The age of threads is coming to a close!
if ($threadID) {
    exit(0);
}
while (wait() != -1) {}


# Let the user know they're in the home-stretch!
ReportProgress('final');


# Woo-hoo!  Janitorial work is my favorite!
for ($threadID=0; $threadID<$num_cpus; $threadID++) {

    # Clear out all these files we don't need
    $nucl_seq_fname = $outgenesdir.'nucl.tmp'.$threadID.'.fa';
    $prot_seq_fname = $outgenesdir.'prot.tmp'.$threadID.'.fa';
    $tbn_out_fname  = $outgenesdir.'tbn.tmp'.$threadID.'.out';

    if (-e $nucl_seq_fname) { system("rm $nucl_seq_fname"); }
    if (-e $prot_seq_fname) { system("rm $prot_seq_fname"); }
    if (-e $tbn_out_fname)  { system("rm $tbn_out_fname");  }

    # How'd ya do, helper?
    if ($threadID) {
	
	my $final_infname = $outgenesdir.$threadID.'.final-tally.out';
	my $final_inf = OpenInputFile($final_infname);
    
	my $line = <$final_inf>;
	$line =~ /(\d+) \/ (\d+)/;
	$total_ghosts_busted += $1;
	$total_ghost_exons += $2;
	
	$line = <$final_inf>;
	$line =~ s/\n|\r//g;
	foreach my $gene (split(/\|/,$line)) {
	    push(@GhostlyGenes,$gene);
	}

	# Now erase every last trace of that darn helper from the Earth!
	close($final_inf);
	system("rm $final_infname");

    }
	
}


# This is what we call "the final judgment": did we find *anything*?
if ($total_ghost_exons == 0) {

    # Wowza yowza bo-bowza!  Really?  Nothing?  Okay...
    system("rm -rf $outdirname \&");
    print "\n  No potentially unannotated exons detected\n\n";

    exit(0);

}


# We'll write out summary statistics for the full collection of genes
# that had hits
GetMapSummaryStats(\@GhostlyGenes);


# Additionally, we'll write out the (easier on the eyes) file that lists
# each exon that we found, in order of percent alignment identity.
my $results_overview_str = RecordHitsByPctID();
print "\n$results_overview_str\n";


# THAT'S IT!
print "\n";
print "  Diviner complete; results in $outdirname\n";
print "\n\n";


1;






###################
#                 #
#   SUBROUTINES   #
#                 #
###################






###############################################################
#
#  Function: PrintUsage
#
sub PrintUsage
{
    print "\n";
    print "  USAGE :  ./Diviner.pl {OPT.s} [Mirage-Results] [Species-Guide]\n";
    print "\n";
    print "  OPT.s :  -cpus=[int]\n";
    print "           -outdirname=[string]\n";
    print "           -density=[double]\n";
    die "\n";
}





###############################################################
#
#  Function: DetailedUsage
#
sub DetailedUsage
{
    print "\n";
    print "  USAGE :  ./Diviner.pl {OPT.s} [Mirage-Results] [Species-Guide]\n";
    print "\n";
    print "  OPT.s :  -cpus=[int]          : Set the number of CPU cores to use.\n";
    print "                                  (default:2)\n";
    print "\n";
    print "           -outdirname=[string] : Save program outputs to a directory with the specified name.\n";
    print "                                  (default:Diviner-Results)\n";
    print "\n";
    print "           -density=[double]    : Set the BLOSUM-62 score density threshold for acceptable\n";
    print "                                  alignments between known exons and possible coding regions.\n";
    print "\n";
    print "                                  Recommended range: 1 (distant homologs) to 3 (strong similarity)\n";
    print "                                  (default:1.5)\n";
    die "\n";
}





###############################################################
#
#  Function: ParseArgs
#
sub ParseArgs
{

    my %Options = (
	cpus => 1,
        outdirname => 'Diviner-Results',
        savemsas => 0,
	alicutoff => 0.4,
	density => 2
        );

    &GetOptions( 
        \%Options,
        "help",
	"cpus=i",
        "outdirname=s",
	"savemsas",
	"alicutoff=s",
	"density=s"
        )
        || die "\n  ERROR:  Failed to parse command line arguments\n\n";

    if ($Options{help}) {
	DetailedUsage();
    }

    return \%Options;
    
}




###############################################################
#
#  Function: GetMappedSeqMSA
#
sub GetMappedSeqMSA
{
    my $msa_infname = shift;
    my $gene = shift;

    # Start off by just reading in the MSA as-is
    my ($msa_ref,$seqnames_ref,$base_num_seqs,$base_msa_len) = ParseAFA($msa_infname);
    my @BaseMSA = @{$msa_ref};
    my @BaseSeqNames = @{$seqnames_ref};

    # Now we'll check each of the present species to see who in this
    # family is mapped.
    my %SpeciesToMapfiles;
    my %SpeciesToChr;
    my %MappedSeqs;
    foreach my $seqname (@BaseSeqNames) {

	# NOTE: We're currently assuming that our names are formatted in
	#       the Mirage-y way.
	# TODO: Change this to accept UniProt formatting
	$seqname =~ /^([^\|]+)\|/;
	my $species = lc($1);

	# If we've already pulled in this species' mapped sequences
	# (or confirmed that this whole species didn't map),
	# then skip right along, ya dinghus!
	next if ($SpeciesToMapfiles{$species});

	# Do we have a mapping file for this gene?
	my $mapfname = $all_species_dirname.$species.'/mappings/'.$gene.'.out';
	if (!(-e $mapfname)) {
	    $SpeciesToMapfiles{$species} = "-1";
	    next;
	}
	$SpeciesToMapfiles{$species} = $mapfname;

	# Oh boy! Time to read a file (right now, all we want is a roster
        # of mapped sequences)
	my $mapf = OpenInputFile($mapfname);
	my $canon_chr;
	while (my $line = <$mapf>) {

	    $line =~ s/\n|\r//g;

	    if ($line =~ /^Canonical Chromosome\: (\S+)/) {

		$canon_chr = $1;
		$SpeciesToChr{$species} = $canon_chr;
		
	    } elsif ($line =~ /^Sequence ID\: (\S+)/) {

		my $mapped_seqname = $1;

		# We'll need to make sure that we've hit on the right chromosome
		$line = <$mapf>; # map method
		$line = <$mapf>; # chromosome
		if ($line =~ /^Chromosome \: (\S+)/) {
		    my $mapped_chr = $1;
		    if ($mapped_chr eq $canon_chr) {
			$MappedSeqs{$mapped_seqname} = 1;
		    }
		}
		
	    }
	    
	}
	close($mapf);
	
    }

    
    # Before we go any further, if there's only one species mapping then we'll
    # bail.  Because 'SpeciesToMapfiles' initially has '-1' for any unmapped
    # species, we'll need to switch those to '0's
    my $num_mapped_species = 0;
    foreach my $species (keys %SpeciesToMapfiles) {
	if ($SpeciesToMapfiles{$species} eq "-1") {
	    $SpeciesToMapfiles{$species} = 0;
	} else {
	    $num_mapped_species++;
	}
    }
    return (0,0,0,0,0,0) if ($num_mapped_species <= 1);
    

    # Awesome!  Now we have a roster of sequences that mapped back to their
    # genomes, so let's take the initial step of reducing our MSA down to just
    # that collection.
    my @MSA;
    my @SeqNames;
    my $num_seqs = 0;
    for (my $i=0; $i<$base_num_seqs; $i++) {
	if ($MappedSeqs{$BaseSeqNames[$i]}) {

	    $SeqNames[$num_seqs] = $BaseSeqNames[$i];

	    for (my $j=0; $j<$base_msa_len; $j++) {
		$MSA[$num_seqs][$j] = $BaseMSA[$i][$j];
	    }
	    $num_seqs++;

	}
    }

    # We'll get rid of any all-gap columns to get our actual msa_len.
    # Note that this will clear any original '/' columns (if we're
    # looking at a dirty MSA), but that's fine since we're re-inserting them.
    my $msa_len = 0;
    for (my $j=0; $j<$base_msa_len; $j++) {
	my $residues = 0;
	for (my $i=0; $i<$num_seqs; $i++) {
	    if ($MSA[$i][$j] =~ /[A-Z]/) {
		$residues = 1;
		last;
	    }
	}
	if ($residues) {
	    for (my $i=0; $i<$num_seqs; $i++) {
		$MSA[$i][$msa_len] = $MSA[$i][$j];
	    }
	    $msa_len++;
	}
    }

    # Phew, that was some good MSA constructing!
    #
    # Next up will be associating each residue with its mapping coordinates
    # and determining where there ought to be splice site boundaries marked.
    #
    my @MapMSA;
    foreach my $species (keys %SpeciesToMapfiles) {

	next if (!$SpeciesToMapfiles{$species});

	my $mapf = OpenInputFile($SpeciesToMapfiles{$species});
	while (my $line = <$mapf>) {

	    # Fast-forward to the next canonically-mapped sequence
	    next if ($line !~ /Sequence ID\: (\S+)/);
	    my $seqname = $1;
	    next if (!$MappedSeqs{$seqname});

	    # We got a mappy boi!  Quick -- what row are you?
	    my $seq_row = 0;
	    while ($SeqNames[$seq_row] ne $seqname) {
		$seq_row++;
	    }

	    # How many exons does this sequence have?
	    $line = <$mapf>; # Map method
	    $line = <$mapf>; # Chromosome
	    $line = <$mapf>; # Num Exons!
	    $line =~ /Num Exons  \: (\d+)/;
	    my $num_exons = $1;

	    # We'll read in the full set of chromosome coordinates for
	    # this sequence before attributing them to MSA positions
	    # (just to simplify writing)
	    my $coord_list_str;
	    for (my $i=0; $i<$num_exons; $i++) {

		$line = <$mapf>; # Exon overview
		$line = <$mapf>; # Coords!

		$line =~ s/\n|\r//g;
		if ($coord_list_str) {
		    $coord_list_str = $coord_list_str.','.$line;
		} else {
		    $coord_list_str = $line;
		}
		
	    }

	    # Now we'll split up our coordinate list string into an
	    # array and walk along the MSA attributing each character
	    # to a coordinate
	    my @CoordList = split(/\,/,$coord_list_str);
	    my $next_coord = 0;
	    my $msa_pos = 0;
	    while ($msa_pos < $msa_len) {
		if ($MSA[$seq_row][$msa_pos] =~ /[A-Z]/) {
		    $MapMSA[$seq_row][$msa_pos] = $CoordList[$next_coord];
		    $next_coord++;
		} else {
		    $MapMSA[$seq_row][$msa_pos] = 0;
		}
		$msa_pos++;
	    }
	    

	}
	close($mapf);
	
    }

    
    # Well that sure gives us a 'MapMSA,' but what if we want to have a
    # splicey MSA?  Have no fear, sweet child, I'm gonna ruin you with
    # splice sites.

    
    # NOTE that the way we'll do this is by first identifying where there
    #   are positions in the MapMSA where the distance between two adjacent
    #   residues is >4, and recording all of those positions.
    my @LastCoord;
    for (my $i=0; $i<$num_seqs; $i++) {
	$LastCoord[$i] = 0;
    }
    
    # This will mark the first amino acid in each exon
    my %SpliceCols; 
    for (my $j=0; $j<$msa_len; $j++) {
	for (my $i=0; $i<$num_seqs; $i++) {
	    if ($MapMSA[$i][$j]) {
		if (abs($LastCoord[$i]-$MapMSA[$i][$j])>4) {
		    if ($SpliceCols{$j}) { $SpliceCols{$j}++; }
		    else                 { $SpliceCols{$j}=1; }
		}
		$LastCoord[$i] = $MapMSA[$i][$j];
	    }
	}
    }

    # Now we'll resolve any splice-sites that aren't universally agreed upon
    # by the sequences that have residues at the given positions.
    # We'll be (specifically) looking to discount columns where the
    # sequences who want the splice-site are immediately following a gap
    # (these look more like alt 3' splice sites), and then requiring that
    # the majority of non-gap-adjacent residues also call a given splice site.
    my @SpliceColList = sort {$a <=> $b} keys %SpliceCols;
    my @VetoedCols;
    my @VetoedColsVotes;
    for (my $splice_col_id=1; $splice_col_id<scalar(@SpliceColList); $splice_col_id++) { # '0' is mandatory

	my $splice_col = $SpliceColList[$splice_col_id];

	# How many sequences have a residue at *both* this column and the
	# last, and want it to be a splice site?
	my $paired_residue_for = 0;
	my $paired_residue_against = 0;
	for (my $i=0; $i<$num_seqs; $i++) {
	    if ($MSA[$i][$splice_col] =~ /[A-Z]/ && $MSA[$i][$splice_col-1] =~ /[A-Z]/) {

                # DEBUGGING
		if (!($MapMSA[$i][$splice_col] && $MapMSA[$i][$splice_col-1])) {
		    print "Mapping issue around col $splice_col in '$SeqNames[$i]'\n";
		    next;
		}
		
		if (abs($MapMSA[$i][$splice_col]-$MapMSA[$i][$splice_col-1])>4) {
		    $paired_residue_for++;
		} else {
		    $paired_residue_against++;
		}

	    }
	}

	# Has this splice site been vetoed?
	if ($paired_residue_against && $paired_residue_against >= $paired_residue_for) {
	    push(@VetoedCols,$splice_col);
	    push(@VetoedColsVotes,$SpliceCols{$splice_col});
	    $SpliceCols{$splice_col} = 0;
	    next;
	}
	
    }

    # If we had a run of vetoed columns that are close (1 or 2 residues apart) and
    # add up to majority support, then we'll re-introduce one of them into the list.
    my $run_start;
    my $run_end=1;
    while ($run_end < scalar(@VetoedCols)-1) {

	# Are we in a run of vetoed columns?
	$run_start = $run_end;
	$run_end++;
	my $run_votes = $VetoedColsVotes[$run_start];
	while ($run_end < scalar(@VetoedCols) && $VetoedCols[$run_end] - $VetoedCols[$run_end-1] < 3) {
	    $run_votes += $VetoedColsVotes[$run_end];
	    $run_end++;
	}

	# If there isn't a run of nearby vetoes, then we'll move right along
	next if ($run_end == $run_start+1);

	# Count the number of sequences that have non-gap characters
	# at one of the vetoed columns
	my $non_gappers = 0;
	for (my $i=0; $i<$num_seqs; $i++) {
	    for (my $col_id=$run_start; $col_id<$run_end; $col_id++) {
		my $msa_pos = $VetoedCols[$col_id];
		if ($MapMSA[$i][$msa_pos] || $MapMSA[$i][$msa_pos-1]) {
		    $non_gappers++;
		    last;
		}
	    }
	}

	# If enough columns have been vetoed to form a majority, then the most
	# used of the group will be designated a splice site.
	next if ($non_gappers >= $run_votes*2);

	my $top_veto_col = $run_start;
	my $top_veto_vote = $VetoedColsVotes[$run_start];
	for (my $i=$run_start+1; $i<$run_end; $i++) {
	    if ($top_veto_vote < $VetoedColsVotes[$i]) {
		$top_veto_col = $i;
		$top_veto_vote = $VetoedColsVotes[$i];
	    }
	}

	# THE PEOPLE HAVE SPOKEN!
	$SpliceCols{$top_veto_col} = $run_votes;
	
    }

    # Get the final list of splice site columns
    @SpliceColList = sort {$a <=> $b} keys %SpliceCols;

    # Now we construct the final splice-site-ified MSAs!
    my @SplicedMSA;
    my @SplicedMapMSA;
    my $spliced_msa_len = 0;
    my $splice_col_id = 0;
    for (my $j=0; $j<$msa_len; $j++) {

	# Have we hit our next splice column?
	if ($splice_col_id < scalar(@SpliceColList) && $SpliceColList[$splice_col_id] == $j) {
	    for (my $i=0; $i<$num_seqs; $i++) {
		$SplicedMSA[$i][$spliced_msa_len] = '/';
		$SplicedMapMSA[$i][$spliced_msa_len] = 0;
	    }
	    $spliced_msa_len++;
	    $splice_col_id++;
	}

	for (my $i=0; $i<$num_seqs; $i++) {
	    $SplicedMSA[$i][$spliced_msa_len] = $MSA[$i][$j];
	    $SplicedMapMSA[$i][$spliced_msa_len] = $MapMSA[$i][$j];
	}
	$spliced_msa_len++;

    }

    # Finally, round things out with a splice site column
    for (my $i=0; $i<$num_seqs; $i++) {
	$SplicedMSA[$i][$spliced_msa_len] = '/';
	$SplicedMapMSA[$i][$spliced_msa_len] = 0;
    }
    $spliced_msa_len++;

    # Pass everything we got back on up the chain of command!
    return (\@SplicedMSA,\@SplicedMapMSA,\@SeqNames,$num_seqs,$spliced_msa_len,\%SpeciesToChr);
    
}





###############################################################
#
#  Function: ParseAFA
#
sub ParseAFA
{
    my $fname = shift;

    my $inf = OpenInputFile($fname);
    my $num_seqs = -1;
    my $msa_len;
    my @MSA;
    my @SeqNames;
    while (my $line = <$inf>) {

	$line =~ s/\n|\r//g;
	next if (!$line);

	if ($line =~ /\>(\S+)/) {

	    my $seqname = $1;
	    push(@SeqNames,$seqname);
	    $num_seqs++;
	    $msa_len = 0;

	} else {

	    foreach my $char (split(//,$line)) {
		$MSA[$num_seqs][$msa_len] = uc($char);
		$msa_len++;
	    }

	}
	
    }
    close($inf);

    $num_seqs++;

    return(\@MSA,\@SeqNames,$num_seqs,$msa_len);

}





###############################################################
#
#  Function: RecordSplicedMSA
#
sub RecordSplicedMSA
{

    my $msa_ref = shift;
    my $seqnames_ref = shift;
    my $num_seqs = shift;
    my $msa_len = shift;
    my $outfname = shift;

    my @MSA = @{$msa_ref};
    my @SeqNames = @{$seqnames_ref};
    
    my $outf = OpenOutputFile($outfname);
    for (my $i=0; $i<$num_seqs; $i++) {

	print $outf ">$SeqNames[$i]\n";
	for (my $j=0; $j<$msa_len; $j++) {
	    print $outf "$MSA[$i][$j]";
	    print $outf "\n" if (($j+1) % 60 == 0);
	}
	print $outf "\n" if ($msa_len % 60);
	#print $outf "\n";
	
    }
    close($outf);

}




###############################################################
#
#  Function: RecordSplicedMap
#
sub RecordSplicedMap
{

    my $msa_ref = shift;
    my $map_msa_ref = shift;
    my $species_names_ref = shift;
    my $species_to_chrs_ref = shift;
    my $num_species = shift;
    my $msa_len = shift;
    my $outfname = shift;

    my @MSA = @{$msa_ref};
    my @MapMSA = @{$map_msa_ref};
    my @SpeciesNames = @{$species_names_ref};
    my %SpeciesToChrs = %{$species_to_chrs_ref};
    
    my $outf = OpenOutputFile($outfname);
    for (my $i=0; $i<$num_species; $i++) {

	my $species = $SpeciesNames[$i];
	my $chr = $SpeciesToChrs{$species};

	my @ExonMaps;
	my $num_exons = 0;
	my $exon_maps_str = '';
	for (my $j=0; $j<$msa_len; $j++) {

	    next if ($MSA[$i][$j] eq '-');

	    if ($MSA[$i][$j] eq '/') {
		if ($exon_maps_str) {
		    push(@ExonMaps,$exon_maps_str);
		    $num_exons++;
		}
		$exon_maps_str = '';
	    } elsif ($exon_maps_str) {
		$exon_maps_str = $exon_maps_str.','.$MapMSA[$i][$j];
	    } else {
		$exon_maps_str = $MapMSA[$i][$j];
	    }
	    
	}

	print $outf "Species    : $species\n";
	print $outf "Chromosome : $chr\n";
	print $outf "Num Exons  : $num_exons\n";

	my $species_num_aminos = 0;
	for (my $j=0; $j<$num_exons; $j++) {

	    $species_num_aminos++;

	    my $exon_map_str = $ExonMaps[$j];

	    $exon_map_str =~ /^(\d+)/;
	    my $start_nucl = $1;

	    $exon_map_str =~ /(\d+)$/;
	    my $end_nucl = $1;

	    print $outf "* Aminos $species_num_aminos..";
	    $species_num_aminos += scalar(split(/\,/,$exon_map_str))-1;
	    print $outf "$species_num_aminos, $chr:$start_nucl..$end_nucl\n";

	    print $outf "$exon_map_str\n";
	    
	}

	print $outf "\n";
	
    }
    close($outf);

}





###############################################################
#
#  Function: ReduceMSAToSpecies
#
sub ReduceMSAToSpecies
{
    my $msa_ref = shift;
    my $mapmsa_ref = shift;
    my $seqnames_ref = shift;
    my $num_seqs = shift;
    my $msa_len = shift;

    my @MSA = @{$msa_ref};
    my @MapMSA = @{$mapmsa_ref};
    my @SeqNames = @{$seqnames_ref};

    # First off, who are our species?  Which sequences belong to which species?
    my %SpeciesToSeqIDs;
    for (my $i=0; $i<$num_seqs; $i++) {
	$SeqNames[$i] =~ /^([^\|]+)\|/;
	my $species = $1;
	if ($SpeciesToSeqIDs{$species}) {
	    $SpeciesToSeqIDs{$species} = $SpeciesToSeqIDs{$species}.','.($i+1);
	} else {
	    $SpeciesToSeqIDs{$species} = ($i+1);
	}
    }

    # Alrighty! Let's get reducing!
    my @SpeciesNames;
    my @SpeciesMSA;
    my @SpeciesMapMSA;
    my $num_species = 0;
    foreach my $species (keys %SpeciesToSeqIDs) {

	push(@SpeciesNames,$species);

	# Get the sequence IDs for every member of this species.
	# Note that we'll need to decrement by one because we previously
	# had to increment by one (to not throw out sequence '0')
	my @SeqIDs = split(/\,/,$SpeciesToSeqIDs{$species});
	for (my $i=0; $i<scalar(@SeqIDs); $i++) {
	    $SeqIDs[$i] = $SeqIDs[$i]-1;
	}

	# Great!  Now it's time to get reducing!  To do this, we'll just
	# walk along the MSA, and wherever there's a residue-containing
	# column we'll take a poll of what the residue should be, and majority
	# wins
	for (my $j=0; $j<$msa_len; $j++) {

	    # If this is a splice-site column, we can take it super easy
	    if ($MSA[0][$j] eq '/') {
		$SpeciesMSA[$num_species][$j] = '/';
		$SpeciesMapMSA[$num_species][$j] = 0;
		next;
	    }
	    
	    my %Residues;
	    foreach my $seq_id (@SeqIDs) {
		if ($MSA[$seq_id][$j] =~ /[A-Z]/) {
		    if ($Residues{$MSA[$seq_id][$j]}) {
			$Residues{$MSA[$seq_id][$j]}++;
		    } else {
			$Residues{$MSA[$seq_id][$j]}=1;
		    }
		}
	    }

	    # If this is a gap column, we can take it sorta easy
	    if (scalar(keys %Residues) == 0) {
		$SpeciesMSA[$num_species][$j] = '-';
		$SpeciesMapMSA[$num_species][$j] = 0;
		next;
	    }

	    # Alrighty then, who's the lucky residue?
	    my @ResidueList = keys %Residues;
	    my $top_residue = $ResidueList[0];
	    my $top_residue_count = $Residues{$top_residue};
	    for (my $i=1; $i<scalar(@ResidueList); $i++) {
		if ($Residues{$ResidueList[$i]} > $top_residue_count) {
		    $top_residue = $ResidueList[$i];
		    $top_residue_count = $Residues{$top_residue};
		}
	    }

	    # Great stuff!  Now, we just need to get a mapping coordinate from
	    # someone who used the top residue.
	    my $map_coord;
	    foreach my $seq_id (@SeqIDs) {
		if ($MSA[$seq_id][$j] eq $top_residue) {
		    $map_coord = $MapMSA[$seq_id][$j];
		    last;
		}
	    }

	    # Record that residue and mapping coordinate!
	    $SpeciesMSA[$num_species][$j] = $top_residue;
	    $SpeciesMapMSA[$num_species][$j] = $map_coord;
	    
	}

	# Another species in the bag!
	$num_species++;

    }

    # That was too easy!
    return(\@SpeciesMSA,\@SpeciesMapMSA,\@SpeciesNames,$num_species);
    
}





###############################################################
#
#  Function: FindGhostExons
#
sub FindGhostExons
{
    my $gene = shift;
    my $msa_ref = shift;
    my $mapmsa_ref = shift;
    my $speciesnames_ref = shift;
    my $num_species = shift;
    my $msa_len = shift;
    my $speciestochrs_ref = shift;

    my @MSA = @{$msa_ref};
    my @MapMSA = @{$mapmsa_ref};
    my @SpeciesNames = @{$speciesnames_ref};
    my %SpeciesToChrs = %{$speciestochrs_ref};

    # This probably seems *really* dumb, but we're going to enumerate the
    # ungapped position of each amino in each species' MSA
    my @IndexMSA;
    my @SpeciesNumAminos;
    for (my $i=0; $i<$num_species; $i++) {
	my $amino_index=0;
	for (my $j=0; $j<$msa_len; $j++) {
	    if ($MSA[$i][$j] =~ /[A-Za-z]/) {
		$IndexMSA[$i][$j] = ++$amino_index;
	    } else {
		$IndexMSA[$i][$j] = 0;
	    }
	}
	$SpeciesNumAminos[$i] = $amino_index;
    }

    # First off, let's figure out where the starts (inclusive) and ends (exclusive)
    # of our exons are, as well as how many exons we have
    my @ExonStarts;
    my @ExonEnds;
    my $num_exons = 0;
    for (my $j=0; $j<$msa_len; $j++) {
	if ($MSA[0][$j] eq '/') {
	    $num_exons++;
	    push(@ExonEnds,$j) if ($j);
	    push(@ExonStarts,$j+1) if ($j+1 < $msa_len);
	}
    }
    $num_exons--; # We'll have overcounted by one, but that's okie-dokie

    # We'll also want to know how to recover species indices from their names, so...
    my %SpeciesToIndex;
    for (my $i=0; $i<$num_species; $i++) {
	$SpeciesToIndex{$SpeciesNames[$i]} = $i+1;
    }

    # Before we get into the nastiness, we'll set some variables to represent the
    # minimum number of amino acids for 'using an exon' and the maximum number
    # of amino acids for 'not using an exon' -- both Inclusive
    #
    # This is intended to pre-empt any occurrences of micro-exons or other
    # weird nonstandard splicing events that might cause an exon to technically
    # have amino acids in it, but clearly only as an artifact of computation.
    #
    # Similarly, we have a minimum number of aminos for a sequence to be worth
    # tblastn-ing.
    my $min_use_aminos = 6;
    my $max_nonuse_aminos = 3;
    my $min_search_aminos = 10;

    # Alright, now for the pain!  We'll do a pairwise comparison of species,
    # seeing which species suggest ghost exons in which other ones.
    # Wherever we find such pairs, we'll record (1) the sequence we're looking for,
    # (2) the species we're looking for it in, (3) the range we're looking for it in,
    # and (4) the species we found it in.
    my @SearchSeqs;
    my @SearchAminoRanges;
    my @TargetSpecies;
    my @TargetSpeciesRange;
    my @SourceSpecies;
    my @MSAExonRanges;
    my @UsedRegions;
    my $num_ghost_exons = 0;
    for (my $s1=0; $s1<$num_species-1; $s1++) {

	my $species1 = $SpeciesNames[$s1];

	for (my $s2=$s1+1; $s2<$num_species; $s2++) {

	    my $species2 = $SpeciesNames[$s2];

	    # We'll kick things off by computing the number of matches / mismatches
	    # between the two sequences, as well as the total number of amino acids
	    # each sequence has, for each exon.  We'll use these bits of information
	    # to make a determination as to the nastiness of the pairing.
	    my @ExonMatches;
	    my @ExonMismatches;
	    my @ExonPctsID;
	    my @S1ExonAminos;
	    my @S2ExonAminos;
	    my @IsNastyExonPair;
	    my @IsUsedAtAll;
	    my @MicroExonic;
	    for (my $exon_id=0; $exon_id<$num_exons; $exon_id++) {

		$ExonMatches[$exon_id] = 0;
		$ExonMismatches[$exon_id] = 0;
		$S1ExonAminos[$exon_id] = 0;
		$S2ExonAminos[$exon_id] = 0;

		# Let's start with the straight facts
		for (my $j=$ExonStarts[$exon_id]; $j<$ExonEnds[$exon_id]; $j++) {

		    if ($MSA[$s1][$j] =~ /[A-Z]/) {
			$S1ExonAminos[$exon_id]++;
			if ($MSA[$s2][$j] =~ /[A-Z]/) {
			    $S2ExonAminos[$exon_id]++;
			    if ($MSA[$s1][$j] eq $MSA[$s2][$j]) {
				$ExonMatches[$exon_id]++;
			    } else {
				$ExonMismatches[$exon_id]++;
			    }
			}
		    } elsif ($MSA[$s2][$j] =~ /[A-Z]/) {
			$S2ExonAminos[$exon_id]++;
		    }
		    
		}


		# But now it's time for a hot take!
		$ExonPctsID[$exon_id] = 0;
		$IsNastyExonPair[$exon_id] = 0;
		$MicroExonic[$exon_id] = 0;
		$IsUsedAtAll[$exon_id] = 1;

		# Catch micro exons
		if ($S1ExonAminos[$exon_id] <= $max_nonuse_aminos
		    || $S2ExonAminos[$exon_id] <= $max_nonuse_aminos) {
		    $MicroExonic[$exon_id] = 1;
		}

		if ($ExonMismatches[$exon_id] || $ExonMatches[$exon_id]) {
		    $ExonPctsID[$exon_id] = 100.0 * $ExonMatches[$exon_id] / ($ExonMatches[$exon_id]+$ExonMismatches[$exon_id]+0.0);
		} else {
		    $IsNastyExonPair[$exon_id] = 0;
		    if ($S1ExonAminos[$exon_id] == 0 && $S2ExonAminos[$exon_id] == 0) {
			$IsUsedAtAll[$exon_id] = 0;
		    }
		    next;
		}

		# If we have a micro exon we'll go ahead an bail (but we do
		# hang onto the pct id for some reason...)
		next if ($MicroExonic[$exon_id]);

		# Way to nastiness 1: One sequence doesn't use this exon, but
		#   the other does.
		#
		if ($S1ExonAminos[$exon_id] >= $min_use_aminos
		    && $S2ExonAminos[$exon_id] <= $max_nonuse_aminos) {
		    $IsNastyExonPair[$exon_id] = 1;
		    next;
		}
		if ($S2ExonAminos[$exon_id] >= $min_use_aminos
		    && $S1ExonAminos[$exon_id] <= $max_nonuse_aminos) {
		    $IsNastyExonPair[$exon_id] = 1;
		    next;
		}

		# Way to nastiness 2: Both sequences use this exon, but the
		#   total number of aligned columns (matches or mismatches)
		#   is less than half of the length of the shorter of the two
		if (2*($ExonMatches[$exon_id]+$ExonMismatches[$exon_id])
		    < Min($S1ExonAminos[$exon_id],$S2ExonAminos[$exon_id])) {
		    $IsNastyExonPair[$exon_id] = 2;
		    next;
		}

		# Way to nastiness 3: The sequences have a reasonable alignment
		#   region, but the alignment itself is ultra-low-quality.
		my $pct_id = (0.0 + $ExonMatches[$exon_id]) / (0.0 + $ExonMatches[$exon_id] + $ExonMismatches[$exon_id]);
		if ($pct_id <= $bad_ali_cutoff) {
		    $IsNastyExonPair[$exon_id] = 3;
		    next;
		}

	    }

	    # The last thing we'll do to identify nasty exon pairs is check
	    # for drops in alignment quality.  I'm going to bump this over to
	    # a seperate function.
	    my $quality_drops_ref = FindAliQualityDrops(\@ExonPctsID,$num_exons);
	    if ($quality_drops_ref) {
		foreach my $exon_id (@{$quality_drops_ref}) {
		    if ($IsNastyExonPair[$exon_id] == 0) {
			$IsNastyExonPair[$exon_id] = 4;
		    }
		}
	    }

	    # Just kidding about the last time I said 'this is the last thing
	    # we'll do...' Now it's time to let our NastyExons (tm) seep into
	    # any adjacent micro exons.
	    # We'll do this in a forward and a backward pass
	    my $in_nasty_zone = $IsNastyExonPair[0];
	    for (my $exon_id=0; $exon_id<$num_exons; $exon_id++) {
		next if (!$IsUsedAtAll[$exon_id]);
		if ($MicroExonic[$exon_id] && $in_nasty_zone) {
		    $IsNastyExonPair[$exon_id] = 5;
		} else {
		    $in_nasty_zone = $IsNastyExonPair[$exon_id];
		}
	    }

	    for (my $exon_id=$num_exons-1; $exon_id>=0; $exon_id--) {
		next if (!$IsUsedAtAll[$exon_id]);
		if ($MicroExonic[$exon_id] && $in_nasty_zone) {
		    $IsNastyExonPair[$exon_id] = 5;
		} else {
		    $in_nasty_zone = $IsNastyExonPair[$exon_id];
		}
	    }

	    # Radical!  Now we can condense each of our runs of contiguous
	    # nasty exon pairs, extract the relevant sequence, and BOOM!
	    #
	    # NOTE: We don't really need the Matches/Mismatches/S_ExonAminos,
	    #   but it might be good to have at some later point for either
	    #   debugging or more sprawling output, so let's not worry about
	    #   the (probably) unnecessary data hoarding.
	    my @NastyRunStarts;
	    my @NastyRunEnds;
	    my $num_nasty_runs = 0;
	    for (my $exon_id=0; $exon_id<$num_exons; $exon_id++) {
		if ($IsNastyExonPair[$exon_id]) {
		    if ($num_nasty_runs == 0 || $NastyRunEnds[$num_nasty_runs-1] != $exon_id-1) {
			$NastyRunStarts[$num_nasty_runs] = $exon_id;
			$num_nasty_runs++;
		    }
		    $NastyRunEnds[$num_nasty_runs-1] = $exon_id;
		}
	    }

	    # Moment of truth -- are we... NASTY?!
	    next if ($num_nasty_runs == 0);

	    # NASTY! NASTY! NASTY!

	    # Alrighty then, time to take each of our runs and pull out the data
	    # that we'll need to perform our tblastn searches.
	    for (my $run_id=0; $run_id<$num_nasty_runs; $run_id++) {

		my $start_exon = $NastyRunStarts[$run_id];
		my $end_exon = $NastyRunEnds[$run_id];

		my $s1_start_amino = 0;
		my $s1_end_amino   = 0;

		my $s2_start_amino = 0;
		my $s2_end_amino   = 0;

		# The sequence from seq (species) 1 & the sequence from seq 2
		my $search_seq_1 = '';
		my $search_seq_2 = '';
		for (my $j=$ExonStarts[$start_exon]; $j<$ExonEnds[$end_exon]; $j++) {
		    if ($MSA[$s1][$j] =~ /[A-Z]/) {
			$search_seq_1 = $search_seq_1.$MSA[$s1][$j];
			$s1_start_amino = $IndexMSA[$s1][$j] if (!$s1_start_amino);
			$s1_end_amino   = $IndexMSA[$s1][$j];
		    }
		    if ($MSA[$s2][$j] =~ /[A-Z]/) {
			$search_seq_2 = $search_seq_2.$MSA[$s2][$j];
			$s2_start_amino = $IndexMSA[$s2][$j] if (!$s2_start_amino);
			$s2_end_amino   = $IndexMSA[$s2][$j];
		    }
		}

		# We'll be searching for this sequence from species 1 against
		# the genome of species 2.
		if (length($search_seq_1) >= $min_search_aminos) {

		    # [1] Find the nearest genomic coordinates outside of the nasty
		    #     region for sequence 2, starting with the left

		    my $left_nucl_bound;
		    if ($start_exon) {
			my $j=$ExonEnds[$start_exon-1]-1;
			while ($j) {
			    if ($MapMSA[$s2][$j]) {
				$left_nucl_bound = $MapMSA[$s2][$j];
				last;
			    }
			    $j--;
			}
		    }
		    if (!$left_nucl_bound) {
			my $j=0;
			while (!$MapMSA[$s2][$j]) {
			    $j++;
			}
			$left_nucl_bound = '[start-of-coding-region:'.$MapMSA[$s2][$j].']';
		    }

		    # [2] Find the coordinates to the right using a method that mirrors
		    #     how we got coordinates to the left

		    my $right_nucl_bound;
		    if ($end_exon+1 < $num_exons) {
			my $j=$ExonStarts[$end_exon+1];
			while ($j<$msa_len) {
			    if ($MapMSA[$s2][$j]) {
				$right_nucl_bound = $MapMSA[$s2][$j];
				last;
			    }
			    $j++;
			}
		    }
		    if (!$right_nucl_bound) {
			# Find the first coordinate for this species, noting it as such
			my $j=$msa_len-1;
			while (!$MapMSA[$s2][$j]) {
			    $j--;
			}
			$right_nucl_bound = '[end-of-coding-region:'.$MapMSA[$s2][$j].']';
		    }

		    
		    # [3] We'll need to disqualify any nucleotides currently identified
		    #     as contributing to our mapping, so we'll go exon-by-exon and
		    #     record any already-used regions.

		    my $used_regions_str;
		    for (my $exon_id=$start_exon; $exon_id<=$end_exon; $exon_id++) {

			my $region_start;
			for (my $j=$ExonStarts[$exon_id]; $j<$ExonEnds[$exon_id]; $j++) {
			    if ($MapMSA[$s2][$j]) {
				$region_start = $MapMSA[$s2][$j];
				last;
			    }
			}

			my $region_end;
			for (my $j=$ExonEnds[$exon_id]; $j>$ExonStarts[$exon_id]; $j--) {
			    if ($MapMSA[$s2][$j]) {
				$region_end = $MapMSA[$s2][$j];
				last;
			    }
			}

			if ($region_start && $region_end) {
			    if ($used_regions_str) {
				$used_regions_str = $used_regions_str.'&'.$region_start.'|'.$region_end;
			    } else {
				$used_regions_str = $region_start.'|'.$region_end;
			    }
			}
			
		    }

		    # Just to make sure we're sticking something into our list
		    if (!$used_regions_str) {
			$used_regions_str = '0|0';
		    }


		    # Heck yeah! Let's scream (and shout)!
		    push(@SearchSeqs,lc($search_seq_1));
		    push(@SearchAminoRanges,$s1_start_amino.'..'.$s1_end_amino);
		    push(@TargetSpecies,$species2);
		    push(@TargetSpeciesRange,$left_nucl_bound.'|'.$right_nucl_bound);
		    push(@SourceSpecies,$species1);
		    push(@MSAExonRanges,($start_exon+1).'..'.($end_exon+1));
		    push(@UsedRegions,$used_regions_str);
		    $num_ghost_exons++;
		    
		}


		# We'll be searching for this sequence from species 2 against
		# the genome of species 1.
		if (length($search_seq_2) >= $min_search_aminos) {

		    # [1] Find the nearest genomic coordinates outside of the nasty
		    #     region for sequence 1, starting with the left

		    my $left_nucl_bound;
		    if ($start_exon) {
			my $j=$ExonEnds[$start_exon-1]-1;
			while ($j) {
			    if ($MapMSA[$s1][$j]) {
				$left_nucl_bound = $MapMSA[$s1][$j];
				last;
			    }
			    $j--;
			}
		    }
		    if (!$left_nucl_bound) {
			my $j=0;
			while (!$MapMSA[$s1][$j]) {
			    $j++;
			}
			$left_nucl_bound = '[start-of-coding-region:'.$MapMSA[$s1][$j].']';
		    }

		    # [2] Find the coordinates to the right using a method that mirrors
		    #     how we got coordinates to the left

		    my $right_nucl_bound;
		    if ($end_exon+1 < $num_exons) {
			my $j=$ExonStarts[$end_exon+1];
			while ($j<$msa_len) {
			    if ($MapMSA[$s1][$j]) {
				$right_nucl_bound = $MapMSA[$s1][$j];
				last;
			    }
			    $j++;
			}
		    }
		    if (!$right_nucl_bound) {
			# Find the first coordinate for this species, noting it as such
			my $j=$msa_len-1;
			while (!$MapMSA[$s1][$j]) {
			    $j--;
			}
			$right_nucl_bound = '[end-of-coding-region:'.$MapMSA[$s1][$j].']';
		    }


		    # [3] We'll need to disqualify any nucleotides currently identified
		    #     as contributing to our mapping, so we'll go exon-by-exon and
		    #     record any already-used regions.

		    my $used_regions_str;
		    for (my $exon_id=$start_exon; $exon_id<=$end_exon; $exon_id++) {

			my $region_start;
			for (my $j=$ExonStarts[$exon_id]; $j<$ExonEnds[$exon_id]; $j++) {
			    if ($MapMSA[$s1][$j]) {
				$region_start = $MapMSA[$s1][$j];
				last;
			    }
			}

			my $region_end;
			for (my $j=$ExonEnds[$exon_id]; $j>$ExonStarts[$exon_id]; $j--) {
			    if ($MapMSA[$s1][$j]) {
				$region_end = $MapMSA[$s1][$j];
				last;
			    }
			}

			if ($region_start && $region_end) {
			    if ($used_regions_str) {
				$used_regions_str = $used_regions_str.'&'.$region_start.'|'.$region_end;
			    } else {
				$used_regions_str = $region_start.'|'.$region_end;
			    }
			}
			
		    }

		    # Just to make sure we're sticking something into our list
		    if (!$used_regions_str) {
			$used_regions_str = '0|0';
		    }


		    # Heck yeah! Let's shout (and scream)!
		    push(@SearchSeqs,lc($search_seq_2));
		    push(@SearchAminoRanges,$s2_start_amino.'..'.$s2_end_amino);
		    push(@TargetSpecies,$species1);
		    push(@TargetSpeciesRange,$left_nucl_bound.'|'.$right_nucl_bound);
		    push(@SourceSpecies,$species2);
		    push(@MSAExonRanges,($start_exon+1).'..'.($end_exon+1));
		    push(@UsedRegions,$used_regions_str);
		    $num_ghost_exons++;
		    
		}

		
	    }

	}
	
    }

    # I tried so hard, and got so far, but in the end it still mattered just a lil' bit
    return (0,0) if ($num_ghost_exons == 0);
    
    # NOICE!  Time to get ready for some good 'n' nasty tblastn-ery!

    # We'll tally up the number of successes
    my $ghosts_busted = 0;

    # Prepare to write some stuff to a file!
    my $outf = OpenOutputFile($outgenesdir.$gene.'/search.out');

    # We'll just go hit-by-hit, because that's what's sensible.  'q' for query
    for (my $q=0; $q<$num_ghost_exons; $q++) {

	# Write out the protein sequence to our protein sequence file.
	# We don't use my fancy file functions here because we'll be overwriting.
	open(my $protf,'>',$prot_seq_fname);
	print $protf ">seq\n$SearchSeqs[$q]\n\n";
	close($protf);

	# What's our search chromosome? What are our nucleotide coords?
	my $target_species = $TargetSpecies[$q];
	my $chr = $SpeciesToChrs{$target_species};
	my $revcomp = 0;
	if ($chr =~ /\[revcomp\]/) {
	    $chr =~ s/\[revcomp\]//;
	    $revcomp = 1;
	}

	my @SearchRanges = split(/\|/,$TargetSpeciesRange[$q]);

	# If we're at either terminii of our sequence, pull in an extra 25k (or as
	# much as we can)
	my $terminal_search_dist = 25000;
	if ($SearchRanges[0] =~ /\:(\d+)/) {
	    my $seq_start = $1;
	    if ($revcomp) {
		$SearchRanges[0] = Min($seq_start+$terminal_search_dist,$ChrLensBySpecies{$target_species.'|'.$chr});		
	    } else {
		$SearchRanges[0] = Max($seq_start-$terminal_search_dist,1);
	    }
	}
	
	if ($SearchRanges[1] =~ /\:(\d+)/) {
	    my $seq_end = $1;
	    if ($revcomp) {
		$SearchRanges[1] = Max($seq_end-$terminal_search_dist,1);
	    } else {
		$SearchRanges[1] = Min($seq_end+$terminal_search_dist,$ChrLensBySpecies{$target_species.'|'.$chr});
	    }
	}

	# Well, we sure know what sequence to pull in now, don't we!
	my $sfetch_cmd = $sfetch.' -range '.$SearchRanges[0].'..'.$SearchRanges[1];
	$sfetch_cmd = $sfetch_cmd.' '.$SpeciesToGenomes{$target_species}.' '.$chr;
	$sfetch_cmd = $sfetch_cmd.' > '.$nucl_seq_fname;
	RunSystemCommand($sfetch_cmd);

	# Because of the wonders of filename standardization, we can do this!
	RunSystemCommand($tblastn);

	# Grab the list of coordinates that have already been used for mapping this
	# sequence's analog (not the right word, maybe, but you know what I mean).
	my @PrevUsedRegions = split(/\&/,$UsedRegions[$q]);

	# What did we get?
	my @HitAminoStarts;
	my @HitAminoEnds;
	my @HitNuclStarts;
	my @HitNuclEnds;
	my @HitEVals;
	my $num_tbn_hits = 0;
	my $tbnf = OpenInputFile($tbn_out_fname);
	while (my $line = <$tbnf>) {
	    if ($line) {
		
		my @HitData = split(/\s+/,$line);
		my $amino_start = $HitData[6];
		my $amino_end   = $HitData[7];
		my $nucl_start  = $HitData[8];
		my $nucl_end    = $HitData[9];
		my $e_val       = $HitData[10];

		# We'll take notice of any hits with an e-val with a '-'
		next if ($e_val !~ /e\-/);

		# What are the actual nucleotide coords?
		if ($revcomp) {
		    $nucl_start = $SearchRanges[0] - $nucl_start;
		    $nucl_end   = $SearchRanges[0] - $nucl_end;
		} else {
		    $nucl_start += $SearchRanges[0];
		    $nucl_end   += $SearchRanges[0];
		}

		# We need to confirm that this isn't overlapping with any of
		# the nucleotide regions that have been previously used to
		# map this sequence.
		# It also can't fully contain an exon, ding-dong!
		my $was_prev_used = 0;
		foreach my $prev_used_region (@PrevUsedRegions) {

		    $prev_used_region =~ /^(\d+)\|(\d+)$/;
		    my $prev_start = $1;
		    my $prev_end = $2;

		    if ($revcomp) {
			if ($nucl_start <= $prev_start && $nucl_start >= $prev_end) {
			    $was_prev_used = 1;
			    last;
			}
			if ($nucl_end <= $prev_start && $nucl_end >= $prev_end) {
			    $was_prev_used = 1;
			    last;
			}
			if ($nucl_start >= $prev_start && $nucl_end <= $prev_end) {
			    $was_prev_used = 1;
			    last;
			}
		    } else {
			if ($nucl_start >= $prev_start && $nucl_start <= $prev_end) {
			    $was_prev_used = 1;
			    last;
			}
			if ($nucl_end >= $prev_start && $nucl_end <= $prev_end) {
			    $was_prev_used = 1;
			    last;
			}
			if ($nucl_start <= $prev_start && $nucl_end >= $prev_end) {
			    $was_prev_used = 1;
			    last;
			}
		    }

		}

		next if ($was_prev_used);

		push(@HitAminoStarts,$amino_start);
		push(@HitAminoEnds,$amino_end);
		push(@HitNuclStarts,$nucl_start);
		push(@HitNuclEnds,$nucl_end);
		push(@HitEVals,$e_val);
		$num_tbn_hits++;

	    }
	}
	close($tbnf);

	# For outputting, let's get the textual representation of direction
	# into the chromosome name (after recording the chromosome length of
	# our target species, for exon overlap checking).
	my $chr_len = $ChrLensBySpecies{$target_species.'|'.$chr};
	$chr = $chr.'[revcomp]' if ($revcomp);

	# Speaking of outputting, let's just have these tidbits on-hand, too
	my $source_species = $SourceSpecies[$q];

	$MSAExonRanges[$q] =~ /(\d+)\.\.(\d+)/;
	my $start_exon = $1;
	my $end_exon = $2;
	my $exon_str = 'Exon';
	if ($start_exon != $end_exon) {
	    $exon_str = $exon_str.'s '.$start_exon.'..'.$end_exon;
	} else {
	    $exon_str = $exon_str.' '.$end_exon;
	}

	my $target_info = "MSA Ali Region  : $exon_str\n";
	$target_info = $target_info."    Target Genome   : $target_species ($chr:$SearchRanges[0]..$SearchRanges[1])\n";
	$target_info = $target_info."    Source Species  : $source_species (Aminos $SearchAminoRanges[$q])\n";
	
	# Is it an especially elusive ghost we're chasing?
	if ($num_tbn_hits == 0) {
	    print $outf "[ ] Search failure (no tblastn hits)\n";
	    print $outf "    $target_info";
	    print $outf "    Search Sequence : $SearchSeqs[$q]\n\n";
	    next;
	}
	
	# Oh, this is a most profitable Ghost Adventure indeed!
	$ghosts_busted++;

	# Let's illustrate how much of the sequence has been covered.
	# NOTE: We're assuming that our hits are consistent with one another,
	#   but we may want to double-check that in the future...
	my @MappedSeq = split(//,lc($SearchSeqs[$q]));
	for (my $hit=0; $hit<$num_tbn_hits; $hit++) {
	    for (my $pos=$HitAminoStarts[$hit]-1; $pos<$HitAminoEnds[$hit]; $pos++) {
		$MappedSeq[$pos] = uc($MappedSeq[$pos]);
	    }
	}
	my $mapped_seq = '';
	foreach my $char (@MappedSeq) {
	    $mapped_seq = $mapped_seq.$char;
	}

	# Sing it to high heaven!
	print $outf "[+] Search success!\n";
	print $outf "    $target_info";
	print $outf "    Search Sequence : $mapped_seq\n";
	print $outf "    Num tblastn Hits: $num_tbn_hits\n";

	# I'm going to take this 'underlining' out for now, and let the
	# upper / lower case distinction speak for itself.
	#
	#print $outf "    ";
	#foreach my $char (@MappedSeq) {
	#if ($char eq uc($char)) { print $outf '-'; }
	#else                    { print $outf ' '; }
	#}
	#print $outf "\n";

	for (my $hit=0; $hit<$num_tbn_hits; $hit++) {

	    # What aminos (within the species sequence) were part of this hit?
	    $SearchAminoRanges[$q] =~ /(\d+)\.\./;
	    my $hit_amino_start = $HitAminoStarts[$hit];
	    my $hit_amino_end   = $hit_amino_start + ($HitAminoEnds[$hit] - $HitAminoStarts[$hit]);
	    
	    print $outf "    + Aminos $hit_amino_start..$hit_amino_end ";
	    print $outf "mapped to $target_species $chr:$HitNuclStarts[$hit]..$HitNuclEnds[$hit] ";
	    print $outf "($HitEVals[$hit])\n";

	}
	
	print $outf "\n";
	
    }

    close($outf);

    # How'd we do there?
    return ($num_ghost_exons, $ghosts_busted);

}






###############################################################
#
#  Function: FindAliQualityDrops
#
sub FindAliQualityDrops
{
    my $pcts_id_ref = shift;
    my $num_exons = shift;

    my @PctsID = @{$pcts_id_ref};

    # At what drop from a local maximum exon pair's quality
    # do we get concerned?
    my $q_drop_threshold = 25; # rec. 35+ for the alt. approach.

    # To avoid a bookkeeping headache, we'll just do two passes
    # (left-to-right, right-to-left, DUH).
    my @HasQDrop;
    for (my $i=0; $i<$num_exons; $i++) {
	$HasQDrop[$i] = 0;
    }

    my $exon_id = 0;
    while ($PctsID[$exon_id] == 0) {
	$exon_id++;
    }
    my $last_exon_pct_id = $PctsID[$exon_id++];

    while ($exon_id < $num_exons) {
	if ($PctsID[$exon_id]) {
	    if ($last_exon_pct_id - $PctsID[$exon_id] >= $q_drop_threshold) {
		$HasQDrop[$exon_id] = 1;
	    }
	    $last_exon_pct_id = $PctsID[$exon_id];
	}
	$exon_id++;
    }

    # Reverse course!
    # Note that exon_id starts out-of-bounds, so we decrement before anything else
    while ($exon_id) {
	$exon_id--;
	if ($PctsID[$exon_id]) {
	    if ($last_exon_pct_id - $PctsID[$exon_id] >= $q_drop_threshold) {
		$HasQDrop[$exon_id] = 1;
	    }
	    $last_exon_pct_id = $PctsID[$exon_id];
	}	
    }

    # We can imagine a case where we have something like 100/50/45/50/100,
    # but if we stick with what we have now, that middle exon isn't going
    # to be seen as low-quality.
    # To remedy this, we'll run along from each low-quality exon labeling any
    # exons that don't improve by >5% as also low-quality.
    # Again, to simplify this we'll just do a left-to-right and a right-to-left
    # scan.
    while ($exon_id < $num_exons) {
	if ($HasQDrop[$exon_id]) {
	    my $pct_to_beat = $PctsID[$exon_id] + 5.0;
	    $exon_id++;
	    while ($exon_id < $num_exons) {
		if ($PctsID[$exon_id]) {
		    if ($PctsID[$exon_id] < $pct_to_beat) {
			$HasQDrop[$exon_id] = 1;
		    } else {
			last;
		    }
		}
		$exon_id++;
	    }
	} else {
	    $exon_id++;
	}
    }

    while ($exon_id > 0) {
	$exon_id--;
	if ($HasQDrop[$exon_id]) {
	    my $pct_to_beat = $PctsID[$exon_id] + 5.0;
	    $exon_id--;
	    while ($exon_id >= 0) {
		if ($PctsID[$exon_id]) {
		    if ($PctsID[$exon_id] < $pct_to_beat) {
			$HasQDrop[$exon_id] = 1;
		    } else {
			last;
		    }
		}
		$exon_id--;
	    }
	}
    }

    # Phew! So close to being done!
    # Now we just need to get a list of the QDroppers and be on
    # our merry way.
    my @LowQExonPairs;
    for (my $i=0; $i<$num_exons; $i++) {
	if ($HasQDrop[$i]) {
	    push(@LowQExonPairs,$i);
	}
    }

    if (scalar(@LowQExonPairs) == 0) {
	return 0;
    }
    return \@LowQExonPairs;





    ###########################################
    #                                         #
    #  ALT APPROACH: DROP FROM LOCAL MAXIMUM  #
    #                                         #
    ###########################################
    #
    # NOTE: An issue with this method was that we would see some
    #       extremely high-quality exon alignments (e.g., 100%),
    #       from which the alignment quality would slowly walk down
    #       to something like 68%, thus flagging that lower-scoring
    #       exon even if it were flanked by 70s-ish exons.
    #


    # We'll start off by computing the avg. pct ID (ignoring 0s)
    # and initializing an array to store 'quality ratings'
    my $avg_pct_id = 0.0;
    my $num_nonzero = 0;
    my @QualityRatings;
    foreach my $pct_id (@PctsID) {
	push(@QualityRatings,0);
	if ($pct_id) {
	    $avg_pct_id += $pct_id;
	    $num_nonzero++;
	}
    }
    
    if ($num_nonzero) {
	$avg_pct_id /= $num_nonzero;
    } else {
	return 0;
    }

    # Next up, we'll give a '1' to every exon pair that has an
    # alignment quality equal to or above the average and a '-1'
    # to every pair below the average
    my @TopShelfExons;
    for (my $i=0; $i<$num_exons; $i++) {
	if ($PctsID[$i] >= $avg_pct_id) {
	    $QualityRatings[$i] = 1;
	} elsif ($PctsID[$i]) {
	    $QualityRatings[$i] = -1;
	}
    }

    # Find the local maxima.  Note that this isn't "every peak,"
    # but rather a maximum among a set of relatively strong exons.
    my @LocalMaxima;
    for (my $i=0; $i<$num_exons; $i++) {

        if ($QualityRatings[$i] == 1) {

	    my $max_pct = $PctsID[$i];
	    my $max_pos = $i;

	    $i++;
	    while ($i<$num_exons && $QualityRatings[$i] != -1) {
		if ($PctsID[$i] > $max_pct) {
		    $max_pct = $PctsID[$i];
		    $max_pos = $i;
		}
		$i++;
	    }

	    $QualityRatings[$max_pos] = 2;
	    push(@LocalMaxima,$max_pos);
	    
	}
	
    }


    # Now we can run in both directions from each local maximum
    # checking for drops below our q-drop threshold
    foreach my $max_pos (@LocalMaxima) {

	my $pct_id_cutoff = $PctsID[$max_pos] - $q_drop_threshold;

	# Scan left
	for (my $i=$max_pos-1; $i>=0; $i--) {
	    last if ($QualityRatings[$i] == 2);
	    if ($PctsID[$i] && $PctsID[$i] <= $pct_id_cutoff) {
		$QualityRatings[$i] = -2;
	    }
	}
	
	# Scan right
	for (my $i=$max_pos+1; $i<$num_exons; $i++) {
	    last if ($QualityRatings[$i] == 2);
	    if ($PctsID[$i] && $PctsID[$i] <= $pct_id_cutoff) {
		$QualityRatings[$i] = -2;
	    }
	}
	
    }

    # Finally, we can condense our below-threshold exons into a list
    my @QDroppers;
    for (my $i=0; $i<$num_exons; $i++) {
	push(@QDroppers,$i) if ($QualityRatings[$i] == -2);
    }

    return \@QDroppers;
    
}






###############################################################
#
#  Function:  RecordGhostMSAs
#
sub RecordGhostMSAs
{
    my $gene = shift;

    # First things first, we're going to need to grab ahold of this gene's dir
    my $genedir = ConfirmDirectory($outgenesdir.$gene);

    # Open up the file with all of the hits for this gene and read in all
    # successful maps
    my $inf = OpenInputFile($genedir.'search.out');

    my %TargetSpeciesToHits;
    while (my $line = <$inf>) {

	next if ($line !~ /Search success/);

	$line = <$inf>; # MSA position info.
	$line =~ /Exons? (\S+)/;
	my $msa_exons = $1;
	
	$line = <$inf>; # Full target search region
	$line =~ /\: (\S+) \(([^\:]+)\:/;
	my $target_species = $1;
	my $target_chr = $2;
	my $revcomp = 0;
	$revcomp = 1 if ($target_chr =~ /\[revcomp\]/);

	$line = <$inf>; # The source (amino) species
	$line =~ /\: (\S+) \(Aminos (\d+\.\.\d+)\)/;
	my $source_species = $1;
	my $source_amino_range = $2;

	$line = <$inf>; # The sequence searched against the target genome
	$line =~ /\: (\S+)/;
	my $source_seq = uc($1);

	$line = <$inf>; # How many separate tblastn hits did we get?
	$line =~ /\: (\d+)/;
	my $num_tbn_hits = $1;

	# What's the lowest start nucl and highest end nucl (flip for revcomp)?
	my $wide_nucl_start = 0;
	my $wide_nucl_end = 0;

	# Has this exon been annotated in a GTF file provided to Diviner?
	while ($num_tbn_hits) {

	    $line = <$inf>;
	    $num_tbn_hits--;
	    
	    $line =~ /\:(\d+)\.\.(\d+)/;
	    my $hit_nucl_start = $1;
	    my $hit_nucl_end = $2;

	    if ($revcomp) {
		if (!$wide_nucl_start || $hit_nucl_start > $wide_nucl_start) {
		    $wide_nucl_start = $hit_nucl_start;
		}
		if (!$wide_nucl_end || $hit_nucl_end < $wide_nucl_end) {
		    $wide_nucl_end = $hit_nucl_end;
		}
	    } else {
		if (!$wide_nucl_start || $hit_nucl_start < $wide_nucl_start) {
		    $wide_nucl_start = $hit_nucl_start;
		}
		if (!$wide_nucl_end || $hit_nucl_end > $wide_nucl_end) {
		    $wide_nucl_end = $hit_nucl_end;
		}
	    }

	}

	my $wide_nucl_range = $wide_nucl_start.'..'.$wide_nucl_end;

	# Time to record this bad boi!
	my $hash_val = $target_chr.':'.$wide_nucl_range;
	$hash_val = $hash_val.'|'.$source_species.':'.$source_seq.':'.$source_amino_range.':'.$msa_exons;

	if ($TargetSpeciesToHits{$target_species}) {
	    $TargetSpeciesToHits{$target_species} = $TargetSpeciesToHits{$target_species}.'&'.$hash_val;
	} else {
	    $TargetSpeciesToHits{$target_species} = $hash_val;
	}

    }

    close($inf);

    # Make an output directory for our alignment visualizations
    my $gene_ali_dir = CreateDirectory($genedir.'alignments');
    my $num_gene_ali_files = 0;
    
    # Now we can run through our species actually building up some dang MSAs!
    foreach my $target_species (keys %TargetSpeciesToHits) {

	my @AllSpeciesHits = split(/\&/,$TargetSpeciesToHits{$target_species});

	# We'll need to make sure that our hits are split into exon groups
	my $num_exons = 0;
	my @ExonTargetSpecies;
	my @ExonChrs; # Just to be super sure!
	my @ExonNuclStarts;
	my @ExonNuclEnds;
	my @ExonHits;
	foreach my $hit (@AllSpeciesHits) {

	    $hit =~ /^([^\:]+)\:(\d+)\.\.(\d+)/;
	    my $hit_chr = $1;
	    my $hit_start = $2;
	    my $hit_end = $3;

	    $hit =~ /^[^\|]+\|([^\:]+)\:/;
	    my $source_species = $1;

	    my $revcomp = 0;
	    $revcomp = 1 if ($hit_chr =~ /\[revcomp\]/);

	    if (!$num_exons) {
		push(@ExonTargetSpecies,$target_species);
		push(@ExonChrs,$hit_chr);
		push(@ExonNuclStarts,$hit_start);
		push(@ExonNuclEnds,$hit_end);
		$ExonHits[0] = $hit;
		$num_exons++;
		next;
	    }

	    # All overlapping hits (w.r.t. the target species' genome) are grouped
	    # together as an "exon group"
	    my $exon_group = -1;
	    for (my $i=0; $i<$num_exons; $i++) {

		next if ($hit_chr ne $ExonChrs[$i]);

		if ($revcomp) {

		    if (($hit_start >= $ExonNuclStarts[$i] && $hit_end <= $ExonNuclStarts[$i])
			|| ($hit_end <= $ExonNuclEnds[$i] && $hit_start >= $ExonNuclEnds[$i])) {
			$exon_group = $i;
			$ExonNuclStarts[$i] = Max($hit_start,$ExonNuclStarts[$i]);
			$ExonNuclEnds[$i] = Min($hit_end,$ExonNuclEnds[$i]);
			last;
		    }

		} else {
		    
		    if (($hit_start <= $ExonNuclStarts[$i] && $hit_end >= $ExonNuclStarts[$i])
			|| ($hit_end >= $ExonNuclEnds[$i] && $hit_start <= $ExonNuclEnds[$i])) {
			$exon_group = $i;
			$ExonNuclStarts[$i] = Min($hit_start,$ExonNuclStarts[$i]);
			$ExonNuclEnds[$i] = Max($hit_end,$ExonNuclEnds[$i]);
			last;
		    }

		}
		
	    }

	    if ($exon_group == -1) {
		push(@ExonTargetSpecies,$target_species);
		push(@ExonChrs,$hit_chr);
		push(@ExonNuclStarts,$hit_start);
		push(@ExonNuclEnds,$hit_end);
		push(@ExonHits,$hit);
		$num_exons++;
	    } else {
		$ExonHits[$exon_group] = $ExonHits[$exon_group].'&'.$hit;
	    }
	    
	}

	
	# Them's some exons!  Now we can go through each exon-group and generate
	# an MSA representing the translated target sequence and each of the source
	# species' amino acid sequences
	#
	# Reminder: Each "exon" is a group of tblastn hits from "source" species to an
	#   an overlapping region of the "target" genome
	#
	# We'll write out a file with our MSA visualizations for each species
	my $outfname = $gene_ali_dir.$target_species.'.MSAs.out';
	my $outf = OpenOutputFile($outfname);
	for (my $i=0; $i<$num_exons; $i++) {
	    
	    # Start off by getting access to the specific source species matches
	    my @SourceAminoRanges;
	    my @SourceSpecies;
	    my @SourceSeqs;
	    my $msa_start_exon = -1;
            my $msa_end_exon = -1;
	    foreach my $hit (split(/\&/,$ExonHits[$i])) {
		
		$hit =~ /^[^\|]+\|([^\:]+)\:([^\:]+)\:([^\:]+)\:([^\:]+)$/;
		push(@SourceSpecies,$1);
		push(@SourceSeqs,$2);
		push(@SourceAminoRanges,$3);
		my $hit_exon_range = $4;

                my $hit_msa_start_exon;
                my $hit_msa_end_exon;
		if ($hit_exon_range =~ /(\d+)\.\.(\d+)/) {
                    $hit_msa_start_exon = $1;
                    $hit_msa_end_exon = $2;
		} else {
                    $hit_msa_start_exon = $hit_exon_range;
                    $hit_msa_end_exon = $hit_exon_range;
                }

                if ($msa_start_exon == -1 || $hit_msa_start_exon < $msa_start_exon) {
                    $msa_start_exon = $hit_msa_start_exon;
                }
                if ($msa_end_exon == -1 || $hit_msa_end_exon > $msa_end_exon) {
                    $msa_end_exon = $hit_msa_end_exon;
                }

	    }
	    my $num_source_species = scalar(@SourceSpecies);

	    my $chr = $ExonChrs[$i];
	    my $revcomp = 0;
	    if ($chr =~ /\[revcomp\]/) {
		$chr =~ s/\[revcomp\]//;
		$revcomp = 1;
	    }
	    
	    my $search_start = $ExonNuclStarts[$i];
	    my $search_end = $ExonNuclEnds[$i];

	    # We'll pull in just  a lil' bit of extra genomic sequence, for the
	    # good of America.
	    my $extra_window = 10;
	    if ($revcomp) {
		$search_start += $extra_window;
		$search_end -= $extra_window;
	    } else {
		$search_start -= $extra_window;
		$search_end += $extra_window;
	    }

	    my $sfetch_cmd = $sfetch.' -range '.$search_start.'..'.$search_end;
	    $sfetch_cmd = $sfetch_cmd.' '.$SpeciesToGenomes{$target_species}.' '.$chr;
	    my $nucl_inf = OpenSystemCommand($sfetch_cmd);
	    my $header_line = <$nucl_inf>;
	    my $nucl_seq = '';
	    while (my $line = <$nucl_inf>) {
		$line =~ s/\n|\r//g;
		$nucl_seq = $nucl_seq.uc($line);
	    }
	    close($nucl_inf);

	    my @NuclSeq = split(//,$nucl_seq);

	    # Instead of picking an individual reading frame to work with, we'll
	    # track down any regions that have a score density >2 and take note of
	    # which portions of which source sequences are associated with those
	    # regions.

	    # Check which reading frame looks like it's the one we're supposed to be
	    # working with...
	    my @FrameTransStrs;
	    my @AllHits;
	    my @HitSetsByTargetRegion;
	    my $num_hits = 0;
	    for (my $frame=0; $frame<3; $frame++) {

		# Pull in this reading frame
		my $frame_str = '';
		my $trans_str = '';
		my @TransChars;
		for (my $i=$frame; $i+2<scalar(@NuclSeq); $i+=3) {

		    my $codon = $NuclSeq[$i].$NuclSeq[$i+1].$NuclSeq[$i+2];
		    $frame_str = $frame_str.$codon;

		    my $trans_aa = TranslateCodon($codon);
		    $trans_str = $trans_str.$trans_aa;

		    push(@TransChars,$trans_aa);

		}

		push(@FrameTransStrs,$trans_str);

		# For each of our source sequences, we'll get a sorted list of
		# hits (by score density), which we'll then organize into groups
		# that overlap on the target genome.
		my @FrameHitsByTargetRegion;
		for (my $source_id=0; $source_id<scalar(@SourceSeqs); $source_id++) {

		    my @SourceChars = split(//,$SourceSeqs[$source_id]);

		    my ($num_alis,$score_densities_ref,$target_ranges_ref,$source_ranges_ref)
			= GatherBestLocalAlis(\@TransChars,0,\@SourceChars,0);

		    next if (!$num_alis);

		    # NOTE: The "Ranges" here are w.r.t. the sequence implicated
		    #       in the hit (not the actual amino acid coordinates in the
		    #       full sequence)
		    my @ScoreDensities = @{$score_densities_ref};
		    my @TargetRanges = @{$target_ranges_ref};
		    my @SourceRanges = @{$source_ranges_ref};

		    for (my $hit_id=0; $hit_id<scalar(@ScoreDensities); $hit_id++) {

			my $score_density = $ScoreDensities[$hit_id];
			my $target_range = $TargetRanges[$hit_id];
			my $source_range = $SourceRanges[$hit_id];

			push(@AllHits,$score_density.':'.$target_range.'/'.$source_range.'/'.$source_id);

			my $new_range = 1;
			for (my $range_id=0; $range_id<scalar(@FrameHitsByTargetRegion); $range_id++) {

			    $FrameHitsByTargetRegion[$range_id] =~ /^([^\:]+)\:(\S+)$/;
			    
			    my $group_range = $1;
			    my $group_data  = $2;

			    my ($overlap,$overlap_range) = RangesOverlap($group_range,$target_range);
			    
			    if ($overlap) {
				$FrameHitsByTargetRegion[$range_id] = $overlap_range.':'.$group_data.','.$num_hits;
				$new_range = 0;
				last;
			    }
			    
			}

			if ($new_range) {
			    push(@FrameHitsByTargetRegion,$target_range.':'.$frame.':'.$num_hits);
			}

			$num_hits++;
			
		    }
		    
		}

		
		# Now we'll integrate the new set of hits according to
		# the order of the target region
		foreach my $frame_hit_set (@FrameHitsByTargetRegion) {

		    $frame_hit_set =~ /^(\d+)\.\./;
		    my $target_start = $1;

		    my $inserted = 0;

		    for (my $hit_set_id=0; $hit_set_id<scalar(@HitSetsByTargetRegion); $hit_set_id++) {

			$HitSetsByTargetRegion[$hit_set_id] =~ /^(\d+)\.\./;
			my $hit_target_start = $1;

			if ($hit_target_start > $target_start) {

			    splice(@HitSetsByTargetRegion,$hit_set_id,0,$frame_hit_set);
			    $inserted = 1;
			    last;
			    
			}
			
		    }

		    if (!$inserted) {
			push(@HitSetsByTargetRegion,$frame_hit_set);
		    }
		    
		}
				
	    }


	    # Did we not end up with any hit sets to play with?
	    next if (scalar(@HitSetsByTargetRegion) == 0);

	    
	    # NOW IT'S TIME TO PARTY!!!
	    #
	    # Each hit set represents a collection of high-quality (score dense)
	    # alignments between a collection of source sequences and the same
	    # region of the target sequence.
	    #
	    # The goal is to produce a (multiple) sequence alignment representing
	    # how the source amino acid sequence(s) match with the target
	    #
	    foreach my $hit_set (@HitSetsByTargetRegion) {

		$hit_set =~ /(\d+)\.\.(\d+)\:([^\:]+)\:(\S+)$/;
		my $target_start = $1;
		my $target_end = $2;
		my $frame_num = $3;
		my @HitIDs = split(/\,/,$4);

		my $num_matched = scalar(@HitIDs);

		my @HitSourceIDs;
		my @HitSourceStarts;
		my @HitSourceEnds;
		for (my $match_id=0; $match_id<$num_matched; $match_id++) {

		    $AllHits[$HitIDs[$match_id]] =~ /\/(\d+)\.\.(\d+)\/(\d+)$/;

		    # NOTE: These "Ranges" are w.r.t the sequence implicated in the
		    #       hit, not the actual amino acid coordinates
		    $HitSourceStarts[$match_id] = $1;
		    $HitSourceEnds[$match_id] = $2;
		    $HitSourceIDs[$match_id] = $3;

		}


		# Start building the multiple sequence alignment by priming
		# with the first of the source sequences
		my $source_id = $HitSourceIDs[0];
		my @SourceSeqChars = split(//,$SourceSeqs[$source_id]);
		
		my @AminoMSA;
		foreach my $char_id ($HitSourceStarts[0]..$HitSourceEnds[0]) {
		    push(@AminoMSA,$SourceSeqChars[$char_id]);
		}
    
		# And now for the rest of the crew...
		for (my $match_id=1; $match_id<$num_matched; $match_id++) {
		    
		    $source_id = $HitSourceIDs[$match_id];
		    @SourceSeqChars = split(//,$SourceSeqs[$source_id]);
		    
		    my @SourceAliChars;
		    foreach my $char_id ($HitSourceStarts[$match_id]..$HitSourceEnds[$match_id]) {
			push(@SourceAliChars,$SourceSeqChars[$char_id]);
		    }
		    
		    my $amino_msa_ref = MultiAminoSeqAli(\@AminoMSA,\@SourceAliChars);
		    @AminoMSA = @{$amino_msa_ref};
		    
		}
		

		# We align the target sequence last so that it's (perhaps) more of an
		# approximation of aligning to an "exon family profile"
		my @AllTargetChars = split(//,$FrameTransStrs[$frame_num]);
		my @TargetRangeChars;
		foreach my $char_id ($target_start..$target_end) {
		    push(@TargetRangeChars,$AllTargetChars[$char_id]);
		}
		
		my $amino_msa_ref = MultiAminoSeqAli(\@TargetRangeChars,\@AminoMSA);
		@AminoMSA = @{$amino_msa_ref};
		my $amino_msa_len = scalar(@AminoMSA);
		
		
		# What are the actual nucleotide bounds of our putative coding region?
		my $true_nucl_start = $search_start;
		my $true_nucl_end;
		if ($revcomp) {
		    $true_nucl_start -= $frame_num + (3 * $target_start);
		    $true_nucl_end = $true_nucl_start+1 - (3 * scalar(@TargetRangeChars));
		} else {
		    $true_nucl_start += $frame_num + (3 * $target_start);
		    $true_nucl_end = $true_nucl_start-1 + (3 * scalar(@TargetRangeChars));
		}
		
		
		# Next, we'll eat into the MSA from each end until we hit a match column
		my $start_col = 0;
		my $end_col = $amino_msa_len-1;
		
		# As we trim, we want to be sure to capture how many characters get
		# removed from each of our source sequences
		my @SourceStartOffsets;
		my @SourceEndOffsets;
		for (my $match_id=0; $match_id<$num_matched; $match_id++) {
		    $SourceStartOffsets[$match_id] = 0;
		    $SourceEndOffsets[$match_id]   = 0;
		}

		# 1. Checking the left side
		#
		while ($start_col<$amino_msa_len) {
		    
		    my @Col = split(//,$AminoMSA[$start_col]);
		    
		    my $target_char = $Col[0];
		    
		    if ($target_char !~ /[A-Z]/) {

			$start_col++;
			if ($revcomp) { $true_nucl_start -= 3; }
			else          { $true_nucl_start += 3; }

			for (my $match_id=0; $match_id<$num_matched; $match_id++) {
			    if ($Col[$match_id+1] =~ /[A-Za-z]/) {
				$SourceStartOffsets[$match_id]++;
			    }
			}
			
			next;

		    }
		    
		    my $trim_it = 1;
		    for (my $match_id=0; $match_id<$num_matched; $match_id++) {
			if ($Col[$match_id+1] ne '-' && uc($Col[$match_id+1]) eq $target_char) {
			    $trim_it = 0;
			    last;
			}
		    }
		    last if (!$trim_it);
		    
		    $start_col++;
		    if ($revcomp) { $true_nucl_start -= 3; }
		    else          { $true_nucl_start += 3; }
		    
		    for (my $match_id=0; $match_id<$num_matched; $match_id++) {
			if ($Col[$match_id+1] =~ /[A-Za-z]/) {
			    $SourceStartOffsets[$match_id]++;
			}
		    }
		    
		}
		
		
		# 2. Checking the right side
		#
		while ($end_col > $start_col) {
		    
		    my @Col = split(//,$AminoMSA[$end_col]);
		    
		    my $target_char = $Col[0];
		    
		    if ($target_char !~ /[A-Z]/) {

			$end_col--;
			if ($revcomp) { $true_nucl_end += 3; }
			else          { $true_nucl_end -= 3; }

			for (my $match_id=0; $match_id<$num_matched; $match_id++) {
			    if ($Col[$match_id+1] =~ /[A-Za-z]/) {
				$SourceEndOffsets[$match_id]++;
			    }
			}
			
			next;

		    }
		    
		    my $trim_it = 1;
		    for (my $match_id=0; $match_id<$num_matched; $match_id++) {
			if ($Col[$match_id+1] ne '-' && uc($Col[$match_id+1]) eq $target_char) {
			    $trim_it = 0;
			    last;
			}
		    }
		    last if (!$trim_it);
		    
		    $end_col--;
		    if ($revcomp) { $true_nucl_end += 3; }
		    else          { $true_nucl_end -= 3; }
		    
		    for (my $match_id=0; $match_id<$num_matched; $match_id++) {
			if ($Col[$match_id+1] =~ /[A-Za-z]/) {
			    $SourceEndOffsets[$match_id]++;
			}
		    }
		    
		}
		
		
		# 3. As an additional lil' bit o' cleanup, we'll go through each
		#    source sequence individually and trim off any extra leading gaps
		#
		for (my $match_id=0; $match_id<$num_matched; $match_id++) {
		    
		    my $row_id = $match_id+1;

		    # Start offset
		    my $col_id = $start_col;
		    my $offset = 0;

		    my @Col = split(//,$AminoMSA[$col_id]);

		    while ($Col[$row_id] eq '-' || GetB62Score($Col[0],$Col[$row_id]) < 0.0) {

			$offset++ if ($Col[$row_id] ne '-');

			$Col[$row_id] = ' ';
			$AminoMSA[$col_id] = join('',@Col);
			
			@Col = split(//,$AminoMSA[++$col_id]);
			
		    }
		    
		    $SourceStartOffsets[$match_id] += $offset;


		    # End offset
		    $col_id = $end_col;
		    $offset = 0;

		    @Col = split(//,$AminoMSA[$col_id]);
		    
		    while ($Col[$row_id] eq '-' || GetB62Score($Col[0],$Col[$row_id]) < 0.0) {
			
			$offset++ if ($Col[$row_id] ne '-');

			$Col[$row_id] = ' ';
			$AminoMSA[$col_id] = join('',@Col);
			
			@Col = split(//,$AminoMSA[--$col_id]);
			
		    }
		    
		    $SourceEndOffsets[$match_id] += $offset;
		   

		    # Let the record show that the ends are offset!
                    $HitSourceStarts[$match_id] += $SourceStartOffsets[$match_id];
                    $HitSourceEnds[$match_id]   -= $SourceEndOffsets[$match_id];

		    # We also want the HitSourceStart/End coordinates to correspond
		    # to the aminos' positions in the full sequence, not just
		    # relative to the region of interest.
                    $SourceAminoRanges[$HitSourceIDs[$match_id]] =~ /^(\d+)\.\./;
                    my $global_amino_range_start = $1;
                    $HitSourceStarts[$match_id] += $global_amino_range_start;
                    $HitSourceEnds[$match_id]   += $global_amino_range_start;
		    
		    
		}
		
		
		# Let's go out to the genome mappings for each of our source species
		# and figure out what coordinates on their genomes correspond to the
		# exon that we found (lifty-overy-stuffy)
		my @SourceLiftStrs;
		my $MapCoordFile = OpenInputFile($genedir.'genome-mappings.out');
		while (my $line = <$MapCoordFile>) {

		    next if ($line !~ /Species\s+\:\s+(\S+)/);
		    my $species = $1;

		    my $match_id = 0;
		    while ($match_id < $num_matched) {
			if ($SourceSpecies[$HitSourceIDs[$match_id]] eq $species) {
			    last;
			}
			$match_id++;
		    }

		    next if ($match_id >= $num_matched);

		    my $source_start = $HitSourceStarts[$match_id];
		    my $source_end   = $HitSourceEnds[$match_id];

		    my @SourceMapRanges;

		    # Great!  Let's grab some coord.s!
		    $line = <$MapCoordFile>;
		    $line =~ /Chromosome\s+\:\s+(\S+)/;

		    my $source_chr = $1;

		    my $source_revcomp = 0;
		    $source_revcomp = 1 if ($source_revcomp =~ /\[revcomp\]/);

		    $line = <$MapCoordFile>;
		    $line =~ /Num Exons\s+\:\s+(\d+)/;

		    my $source_num_exons = $1;

		    my $lift_str = '';
		    for (my $exon_id=0; $exon_id<$source_num_exons; $exon_id++) {

			
			my $exon_metadata  = <$MapCoordFile>;
			my $coord_list_str = <$MapCoordFile>;

			$exon_metadata =~ /Aminos (\d+)\.\.(\d+)\, \S+\:(\d+)\.\.(\d+)\s*$/;
			my $exon_start_amino = $1;
			my $exon_end_amino   = $2;
			my $exon_start_nucl  = $3;
			my $exon_end_nucl    = $4;

			
			# Are we even in the right ballpark?
			next if ($exon_end_amino < $source_start);


			# Oh, we're in the right ballpark, baby!
			$coord_list_str =~ s/\n|\r//g;
			my @ExonNuclCoords = split(/\,/,$coord_list_str);

			
			# Start with the start
			if ($exon_start_amino >= $source_start) {

			    $lift_str = $lift_str.'/'.$exon_start_nucl;
			    
			} else {

			    my $nucl_coord = $ExonNuclCoords[$source_start - $exon_start_amino];

			    if ($source_revcomp) { $nucl_coord++; }
			    else                 { $nucl_coord--; }

			    $lift_str = $lift_str.'/'.$nucl_coord;

			}

			
			# End with the end
			if ($exon_end_amino <= $source_end) {

			    $lift_str = $lift_str.'..'.$exon_end_nucl;
			    
			} else {

			    my $nucl_coord = $ExonNuclCoords[$source_end - $exon_start_amino];

			    if ($source_revcomp) { $nucl_coord--; }
			    else                 { $nucl_coord++; }

			    $lift_str = $lift_str.'..'.$nucl_coord;

			}

			
			# Have we finished the job?
			last if ($exon_end_amino >= $source_end);

			
		    }

		    $lift_str =~ s/^\///;
		    
		    $SourceLiftStrs[$match_id] = $source_chr.':'.$lift_str;

		}
		close($MapCoordFile);
		

		# Before we extend out, record the true start of the translated sequence
		my $translation_start = $true_nucl_start;
		my $translation_end   = $true_nucl_end;
		
		# The last thing we're going to do is extend out 60 nucls on each side
		# of the alignment...
		my $nucl_ext_len = 60;
		if ($revcomp) {
		    $true_nucl_start += $nucl_ext_len;
		    $true_nucl_end   -= $nucl_ext_len;
		} else {
		    $true_nucl_start -= $nucl_ext_len;
		    $true_nucl_end   += $nucl_ext_len;
		}
		
		
		# Great!  Now that we have our final nucleotide region, let's grab
		# those nucleotides.
		$sfetch_cmd = $sfetch.' -range '.$true_nucl_start.'..'.$true_nucl_end;
		$sfetch_cmd = $sfetch_cmd.' '.$SpeciesToGenomes{$target_species}.' '.$chr;
		$nucl_inf = OpenSystemCommand($sfetch_cmd);
		$header_line = <$nucl_inf>;
		$nucl_seq = '';
		while (my $line = <$nucl_inf>) {
		    $line =~ s/\n|\r//g;
		    next if (!$line);
		    $nucl_seq = $nucl_seq.uc($line);
		}
		close($nucl_inf);
		@NuclSeq = split(//,$nucl_seq);
		
		
		# FINALLY TIME TO SKETCH OUR FINAL MSA
		my @MSA;
		my $msa_len=0;
		
		
		# 1. The lead-in nucleotides
		my $nucl_seq_pos = 0;
		while ($nucl_seq_pos < $nucl_ext_len) {
		    
		    $MSA[0][$msa_len] = ' ';
		    $MSA[1][$msa_len] = lc($NuclSeq[$nucl_seq_pos]);
		    
		    for (my $i=0; $i<$num_matched; $i++) {
			$MSA[$i+2][$msa_len] = ' ';
		    }
		    
		    $nucl_seq_pos++;
		    $msa_len++;
		    
		}
		
		# 2. The amino MSA
		for (my $col_id=$start_col; $col_id<=$end_col; $col_id++) {
		    
		    my @Col = split(//,$AminoMSA[$col_id]);
		    
		    # 2.a. The translated target amino sequence
		    $MSA[0][$msa_len]   = ' ';
		    $MSA[0][$msa_len+1] = $Col[0];
		    $MSA[0][$msa_len+2] = ' ';
		    
		    # 2.b. The target nucleotides
		    if ($Col[0] eq '-') {
			$MSA[1][$msa_len]   = '-';
			$MSA[1][$msa_len+1] = '-';
			$MSA[1][$msa_len+2] = '-';
		    } elsif ($Col[0] eq ' ') {
			$MSA[1][$msa_len]   = lc($NuclSeq[$nucl_seq_pos++]);
			$MSA[1][$msa_len+1] = lc($NuclSeq[$nucl_seq_pos++]);
			$MSA[1][$msa_len+2] = lc($NuclSeq[$nucl_seq_pos++]);
		    } else {
			$MSA[1][$msa_len]   = $NuclSeq[$nucl_seq_pos++];
			$MSA[1][$msa_len+1] = $NuclSeq[$nucl_seq_pos++];
			$MSA[1][$msa_len+2] = $NuclSeq[$nucl_seq_pos++];
		    }
		    
		    # 3.b. The source amino sequence(s)
		    for (my $i=0; $i<$num_matched; $i++) {
			
			$MSA[$i+2][$msa_len]   = ' ';
			
			# Periods for matches, lowercase for mismatches
			if ($Col[$i+1] =~ /[A-Z]/ && $Col[$i+1] eq $Col[0]) {
			    $MSA[$i+2][$msa_len+1] = '.';
			} else {
			    $MSA[$i+2][$msa_len+1] = lc($Col[$i+1]);
			}
			
			$MSA[$i+2][$msa_len+2] = ' ';
			
		    }
		    
		    # PROGRESS!
		    $msa_len += 3;
		    
		}
		
		# 3. The lead-out nucleotides
		while ($nucl_seq_pos < scalar(@NuclSeq)) {
		    $MSA[0][$msa_len] = ' ';
		    $MSA[1][$msa_len] = lc($NuclSeq[$nucl_seq_pos]);
		    for (my $i=0; $i<$num_matched; $i++) {
			$MSA[$i+2][$msa_len] = ' ';
		    }
		    $nucl_seq_pos++;
		    $msa_len++;		
		}
		
		
		# THAT'S IT!
		# Now the only remaining work is the final formatting of the string!
		my $longest_name_len = length($target_species);
		foreach my $source_id (@HitSourceIDs) {
		    my $species = $SourceSpecies[$source_id];
		    if (length($species) > $longest_name_len) {
			$longest_name_len = length($species);
		    }
		}
		$longest_name_len += 4; # Two spaces on either side
		
		my @FormattedNames;
		$FormattedNames[0] = '  '.$target_species.'  ';
		while (length($FormattedNames[0]) < $longest_name_len) {
		    $FormattedNames[0] = ' '.$FormattedNames[0];
		}
		
		$FormattedNames[1] = ' ';
		while (length($FormattedNames[1]) < $longest_name_len) {
		    $FormattedNames[1] = ' '.$FormattedNames[1];
		}
		
		for (my $i=0; $i<$num_matched; $i++) {
		    $FormattedNames[$i+2] = '  '.$SourceSpecies[$HitSourceIDs[$i]].'  ';
		    while (length($FormattedNames[$i+2]) < $longest_name_len) {
			$FormattedNames[$i+2] = ' '.$FormattedNames[$i+2];
		    }
		}

		
		# Now that we've made all of our final adjustments, let's
		# record the number of matches and mismatches for each
		# source sequence (for percent id calculation)
		my @SourceNumMatches;
		my @SourceNumMismatches;
		for (my $i=0; $i<$num_matched; $i++) {
		    $SourceNumMatches[$i] = 0;
		    $SourceNumMismatches[$i] = 0;
		}
		

		# Buffer in the alignment string and let 'er rip!
		my $ali_str = "\n\n";
		my $chars_per_line = 60;
		my $msa_pos = 0;
		while ($msa_pos < $msa_len) {
		    
		    my $next_stop = Min($msa_len,$msa_pos+$chars_per_line);
		    
		    for (my $i=0; $i<$num_matched+2; $i++) {
			
			$ali_str = $ali_str.$FormattedNames[$i];
			
			my $pos = $msa_pos;
			while ($pos < $next_stop) {

			    # Percent ID stuff (only for source seq.s)
			    if ($i>1 && $MSA[$i][$pos] =~ /\S/) {
				if ($MSA[$i][$pos] eq '.') {
				    $SourceNumMatches[$i-2]++;
				} else {
				    $SourceNumMismatches[$i-2]++;
				}
			    }
			    
			    $ali_str = $ali_str.$MSA[$i][$pos++];

			}
			$ali_str = $ali_str."\n";
			
		    }
		    
		    $ali_str = $ali_str."\n\n";
		    
		    $msa_pos += 60;
		    
		}
		$ali_str = $ali_str."\n";

		
		# Before we spit out our alignment string, we'll also make a string with
		# hit metadata.
		
		my @SourcePctsID;
		for (my $i=0; $i<$num_matched; $i++) {
		    
		    my $pct_id = int(1000.0 * $SourceNumMatches[$i] / ($SourceNumMatches[$i] + $SourceNumMismatches[$i]));
		    
		    # Formatting: Will we need to add a '.0'
		    if ($pct_id % 10 == 0) {
			$pct_id = $pct_id / 10.0;
			$pct_id = $pct_id.'.0%';
		    } else {
			$pct_id = $pct_id / 10.0;
			$pct_id = $pct_id.'%';
		    }
		    $pct_id = $pct_id.' alignment identity';
		    
		    push(@SourcePctsID,$pct_id);
		    
		}
		
		
		# Metadata item 1: Target sequence info.
		my $meta_str = "  Target : $target_species $chr";
		$meta_str    = $meta_str.'[revcomp]' if ($revcomp);
		$meta_str    = $meta_str.":$translation_start..$translation_end\n";


		# Prep work for novelty checking
		my $strand = '+';
		if ($revcomp) {
		    $strand = '-';
		    my $tmp = $translation_start;
		    $translation_start = $translation_end;
		    $translation_end = $tmp;
		}
		
		my $mb_range_1 = $target_species.'/'.$chr.$strand.':'.(int($translation_start / 100000));
		my $mb_range_2 = $target_species.'/'.$chr.$strand.':'.(int($translation_end   / 100000));

		if ($SpeciesChrMbRangeToHits{$mb_range_1}) {
		    $SpeciesChrMbRangeToHits{$mb_range_1} = $SpeciesChrMbRangeToHits{$mb_range_1}.'|'.$num_thread_hits;
		} else {
		    $SpeciesChrMbRangeToHits{$mb_range_1} = $num_thread_hits;
		}

		if ($mb_range_2 ne $mb_range_1) {
		    
		    if ($SpeciesChrMbRangeToHits{$mb_range_2}) {
			$SpeciesChrMbRangeToHits{$mb_range_2} = $SpeciesChrMbRangeToHits{$mb_range_2}.'|'.$num_thread_hits;
		    } else {
			$SpeciesChrMbRangeToHits{$mb_range_2} = $num_thread_hits;
		    }
		    
		}

		$ThreadHitNumToFileAndData[$num_thread_hits] = $outfname.'|'.$meta_str;
		$ThreadHitNumToNovelty[$num_thread_hits] = 'Novel';

		$num_thread_hits++;

		
		# Metadata item 2: Where in the species MSA are these source sequences?
		$meta_str = $meta_str."  Source : Species-level MSA exon";
		if ($msa_start_exon == $msa_end_exon) {
		    $meta_str = $meta_str." $msa_start_exon\n";
		} else {
		    $meta_str = $meta_str."s $msa_start_exon..$msa_end_exon\n";
		}

		
		# Metadata item 3: Specific source sequence info.
		for (my $i=0; $i<$num_matched; $i++) {
		    $source_id = $HitSourceIDs[$i];
		    $meta_str  = $meta_str."         : $SourceSpecies[$source_id] / ";
		    $meta_str  = $meta_str."aminos $HitSourceStarts[$i]..$HitSourceEnds[$i] ";
		    $meta_str  = $meta_str."($SourceLiftStrs[$i]) ";
		    $meta_str  = $meta_str."/ $SourcePctsID[$i]\n";
		}
		
		
		# Print the alignment!!!
		print $outf "\n-----------------------------------------------\n\n" if ($i);
		print $outf "\n";
		print $outf "$meta_str";
		print $outf "$ali_str";
		
		
	    }

	}
	    
	# We're officially done with this target species!
	close($outf);
	
	# Do a check to see if we actually reported any hits...
	if (!(-s $outfname)) { RunSystemCommand("rm \"$outfname\""); }
	else                 { $num_gene_ali_files++;                }
	
    }

    # Did we end up not recording a single dang alignment?! RATS!
    if ($num_gene_ali_files == 0) {
	RunSystemCommand("rm -rf \"$gene_ali_dir\"");
    }

}






###############################################################
#
#  Function:  RangesOverlap
#
sub RangesOverlap
{
    my $range1 = shift;
    my $range2 = shift;

    $range1 =~ /^(\d+)\.\.(\d+)$/;
    my $r1_start = $1;
    my $r1_end   = $2;

    $range2 =~ /^(\d+)\.\.(\d+)$/;
    my $r2_start = $1;
    my $r2_end   = $2;

    my $overlap = 0;
    my $full_start = 0;
    my $full_end = 0;
    
    if ($r1_start < $r1_end) {

	# Forward strand (if we're looking at genomic sequence)
	if (($r1_start <= $r2_start && $r1_end >= $r2_start)
	    || ($r2_start <= $r1_start && $r2_end >= $r1_start)) {

	    $overlap = 1;
	    $full_start = Min($r1_start,$r2_start);
	    $full_end = Max($r1_end,$r2_end);
	    
	}

    } elsif (($r1_start >= $r2_start && $r1_end <= $r2_start)
	     || ($r2_start >= $r1_start && $r2_end <= $r1_start)) {

	# Reverse strand
	$overlap = 1;
	$full_start = Max($r1_start,$r2_start);
	$full_end = Min($r1_end,$r2_end);

    }

    return ($overlap,$full_start.'..'.$full_end);
    
}




###############################################################
#
#  Function:  GatherBestLocalAlis
#
#  This is a recursive function used to find as many local alignments between
#  a given target and source as possible.
#
#  We find the best local alignment between the full target and source, and then
#  search the upper-left (defined by the start of the local alignment) and the
#  bottom-right (defined by the end of the local alignment) for their best
#  local alignments, going until the density of the best alignment drops below a
#  threshold or we don't have sufficient space to expect to find a good alignment.
#
sub GatherBestLocalAlis
{
    my $target_chars_ref = shift;
    my $target_start     = shift;

    my $source_chars_ref = shift;
    my $source_start     = shift;
    
    my @TargetChars = @{$target_chars_ref};
    my @SourceChars = @{$source_chars_ref};
    
    my $num_target_chars = scalar(@TargetChars);
    my $num_source_chars = scalar(@SourceChars);
    

    my ($score_density,$target_ali_start,$target_ali_end,$source_ali_start,$source_ali_end)
	= LocalAlign(\@TargetChars,\@SourceChars);


    # Did we not find anything we're excited about?
    return (0,0,0,0) if ($score_density < $score_density_threshold);

    
    my $true_target_ali_start = $target_ali_start + $target_start;
    my $true_target_ali_end   = $target_ali_end   + $target_start;
    
    my $true_source_ali_start = $source_ali_start + $source_start;
    my $true_source_ali_end   = $source_ali_end   + $source_start;

    
    my $target_ali_range = $true_target_ali_start.'..'.$true_target_ali_end;
    my $source_ali_range = $true_source_ali_start.'..'.$true_source_ali_end;


    my $num_alis = 1;
    my @ScoreDensities;
    my @TargetRanges;
    my @SourceRanges;
    
    push(@ScoreDensities,$score_density);
    push(@TargetRanges,$target_ali_range);
    push(@SourceRanges,$source_ali_range);


    # Now we see what's good to the left and right of *this* optimal local alignment
    my $min_ali_len = 8;

    
    my @LeftDensities;
    my @LeftTargetRanges;
    my @LeftSourceRanges;
    if (Min($target_ali_start,$source_ali_start) > $min_ali_len) {

	my @LeftTargetChars;
	for (my $i=0; $i<$target_ali_start; $i++) {
	    push(@LeftTargetChars,$TargetChars[$i]);
	}

	my @LeftSourceChars;
	for (my $j=0; $j<$source_ali_start; $j++) {
	    push(@LeftSourceChars,$SourceChars[$j]);
	}
	
	my ($num_left_alis,$left_dens_ref,$left_target_ranges_ref,$left_source_ranges_ref)
	    = GatherBestLocalAlis(\@LeftTargetChars,$target_start,
				  \@LeftSourceChars,$source_start);

	if ($num_left_alis) {
	    @LeftDensities = @{$left_dens_ref};
	    @LeftTargetRanges = @{$left_target_ranges_ref};
	    @LeftSourceRanges = @{$left_source_ranges_ref};
	}
	
    }

    
    my @RightDensities;
    my @RightTargetRanges;
    my @RightSourceRanges;
    if (Min($num_target_chars-$target_ali_end,$num_source_chars-$source_ali_end)-1 > $min_ali_len) {

	my @RightTargetChars;
	for (my $i=$target_ali_end+1; $i<$num_target_chars; $i++) {
	    push(@RightTargetChars,$TargetChars[$i]);
	}

	my @RightSourceChars;
	for (my $j=$source_ali_end+1; $j<$num_source_chars; $j++) {
	    push(@RightSourceChars,$SourceChars[$j]);
	}
	
	my ($num_right_alis,$right_dens_ref,$right_target_ranges_ref,$right_source_ranges_ref)
	    = GatherBestLocalAlis(\@RightTargetChars,$true_target_ali_end+1,
				  \@RightSourceChars,$true_source_ali_end+1);

	if ($num_right_alis) {
	    @RightDensities = @{$right_dens_ref};
	    @RightTargetRanges = @{$right_target_ranges_ref};
	    @RightSourceRanges = @{$right_source_ranges_ref};
	}
	
    }

    
    # Merge 'em!
    my $left_index = 0;
    my $right_index = 0;
    while ($left_index < scalar(@LeftDensities) && $right_index < scalar(@RightDensities)) {
	
	if ($LeftDensities[$left_index] > $RightDensities[$right_index]) {

	    $ScoreDensities[$num_alis] = $LeftDensities[$left_index];
	    $TargetRanges[$num_alis] = $LeftTargetRanges[$left_index];
	    $SourceRanges[$num_alis] = $LeftSourceRanges[$left_index];

	    $num_alis++;
	    $left_index++;
	    
	} else {

	    $ScoreDensities[$num_alis] = $RightDensities[$right_index];
	    $TargetRanges[$num_alis] = $RightTargetRanges[$right_index];
	    $SourceRanges[$num_alis] = $RightSourceRanges[$right_index];

	    $num_alis++;
	    $right_index++;

	}
	
    }

    while ($left_index < scalar(@LeftDensities)) {

	$ScoreDensities[$num_alis] = $LeftDensities[$left_index];
	$TargetRanges[$num_alis] = $LeftTargetRanges[$left_index];
	$SourceRanges[$num_alis] = $LeftSourceRanges[$left_index];
	
	$num_alis++;
	$left_index++;
	    
    }

    while ($right_index < scalar(@RightDensities)) {
	
	$ScoreDensities[$num_alis] = $RightDensities[$right_index];
	$TargetRanges[$num_alis] = $RightTargetRanges[$right_index];
	$SourceRanges[$num_alis] = $RightSourceRanges[$right_index];
	
	$num_alis++;
	$right_index++;

    }

    return ($num_alis,\@ScoreDensities,\@TargetRanges,\@SourceRanges);
    
}
    




###############################################################
#
#  Function:  LocalAlign
#
sub LocalAlign
{

    my $seq1_ref = shift;
    my $seq2_ref = shift;

    # NOTE: As used in 'GatherBestLocalAlis' the target (translated) sequences
    #       is passed in as Seq1 and the source sequence is passed in as Seq2.

    my @Seq1 = @{$seq1_ref};
    my $len1 = scalar(@Seq1);

    my @Seq2 = @{$seq2_ref};
    my $len2 = scalar(@Seq2);

    my @Matrix;
    for (my $i=0; $i<=$len1; $i++) { $Matrix[$i][0] = 0; }
    for (my $j=0; $j<=$len2; $j++) { $Matrix[0][$j] = 0; }

    # Fill in the matrix
    my $max_i;
    my $max_j;
    my $max_score = 0;
    for (my $i=0; $i<$len1; $i++) {
	for (my $j=0; $j<$len2; $j++) {

	    # Stop codon check (we'll do both Seq1 and Seq2 -- why not?)
	    if ($Seq1[$i] eq '*' || $Seq2[$j] eq '*') {
		$Matrix[$i+1][$j+1] = 0;
		next;
	    }

	    my $match_score = GetB62Score($Seq1[$i],$Seq2[$j]) + $Matrix[$i][$j];

	    $Matrix[$i+1][$j+1] = Max(Max($Matrix[$i+1][$j],$Matrix[$i][$j+1])+$b62_gap,
				      $match_score);

	    $Matrix[$i+1][$j+1] = 0 if ($Matrix[$i+1][$j+1] < 0);

	    if ($max_score < $Matrix[$i+1][$j+1]) {
		$max_score = $Matrix[$i+1][$j+1];
		$max_i = $i+1;
		$max_j = $j+1;
	    }
	    
	}
    }

    return (-1,0,0,0,0) if ($max_score < 25.0);

    # TRACEBACK!
    my $start_i = $max_i;
    my $start_j = $max_j;

    my $penult_i = $max_i;
    my $penult_j = $max_j;

    my $ali_len = 0;
    
    while ($Matrix[$start_i][$start_j] > 0) {

	$penult_i = $start_i;
	$penult_j = $start_j;
	
	my $cell_score = $Matrix[$start_i][$start_j];
	
	my $match_score = GetB62Score($Seq1[$start_i-1],$Seq2[$start_j-1]);

	if ($cell_score == $Matrix[$start_i-1][$start_j-1] + $match_score) {
	    
	    $start_i--;
	    $start_j--;

	} elsif ($cell_score == $Matrix[$start_i-1][$start_j] + $b62_gap) {

	    $start_i--;
	    
	} else {

	    $start_j--;
	    
	}
	
	$ali_len++;

    }

    $start_i = $penult_i;
    $start_j = $penult_j;

    my $score_density = $max_score / $ali_len;


    # FINALLY!  Note that we're returning the original max local score,
    # which may not be representative of where we've trimmed the alignment.
    # NOTE that we need to reduce by 1 because our matrix corresponds to
    #   1-indexed sequences.
    return($score_density,$start_i-1,$max_i-1,$start_j-1,$max_j-1);

}






###############################################################
#
#  Function:  GetB62Score
#
sub GetB62Score
{
    my $seqstr1 = shift;
    my $seqstr2 = shift;

    # If either of our sequences involves a stop codon, we're unhappy
    if ($seqstr1 =~ /\*/ || $seqstr2 =~ /\*/) {
	return -100.0;
    }

    my @Chars1 = split(//,$seqstr1);
    my @Chars2 = split(//,$seqstr2);
    my $len1 = scalar(@Chars1);
    my $len2 = scalar(@Chars2);

    my $score = 0.0;
    my $score_mult = 1.0 / ($len1 * $len2);
    for (my $i=0; $i<$len1; $i++) {

	my $char1 = $Chars1[$i];
	next if (!$AminoIndex{$char1});
	$char1 = $AminoIndex{$char1} * 21;
	
	for (my $j=0; $j<$len2; $j++) {

	    my $char2 = $Chars2[$j];
	    next if (!$AminoIndex{$char2});
	    $char2 = $AminoIndex{$char2};

	    $score += $Blosum62[$char1+$char2] * $score_mult;

	}
    }

    return $score;
    
}






###############################################################
#
#  Function:  MultiAminoSeqAli
#
sub MultiAminoSeqAli
{
    my $seqs_1_ref = shift;
    my $seqs_2_ref = shift;

    my @Seqs1 = @{$seqs_1_ref};
    my @Seqs2 = @{$seqs_2_ref};

    my $len1 = scalar(@Seqs1);
    my $len2 = scalar(@Seqs2);

    my @Matrix;
    for (my $i=0; $i<=$len1; $i++) { $Matrix[$i][0] = $i * $b62_gap; }
    for (my $j=0; $j<=$len2; $j++) { $Matrix[0][$j] = $j * $b62_gap; }

    for (my $i=0; $i<$len1; $i++) {
	for (my $j=0; $j<$len2; $j++) {

	    my $match = GetB62Score($Seqs1[$i],$Seqs2[$j]);

	    $Matrix[$i+1][$j+1] = Max($Matrix[$i][$j] + $match,
				      Max($Matrix[$i][$j+1],$Matrix[$i+1][$j]) + $b62_gap);
	    
	}
    }

    my $gapstr1 = '-';
    while (length($gapstr1) < length($Seqs1[0])) { $gapstr1 = $gapstr1.'-'; }

    my $gapstr2 = '-';
    while (length($gapstr2) < length($Seqs2[0])) { $gapstr2 = $gapstr2.'-'; }

    # Time to back-trace!
    my @Ali;
    my $i=$len1;
    my $j=$len2;
    while ($i && $j) {

	my $match = GetB62Score($Seqs1[$i-1],$Seqs2[$j-1]);

	if ($Matrix[$i][$j] == $Matrix[$i-1][$j-1] + $match) {

	    push(@Ali,$Seqs1[$i-1].$Seqs2[$j-1]);
	    $i--;
	    $j--;

	} elsif ($Matrix[$i][$j] == $Matrix[$i-1][$j] + $b62_gap) {

	    push(@Ali,$Seqs1[$i-1].$gapstr2);
	    $i--;

	} else {

	    push(@Ali,$gapstr1.$Seqs2[$j-1]);
	    $j--;

	}

    }

    while ($i) {

	push(@Ali,$Seqs1[$i-1].$gapstr2);
	$i--;

    }

    while ($j) {

	push(@Ali,$gapstr1.$Seqs2[$j-1]);
	$j--;

    }

    # Uh-oh!  That alignment is BACKWARDS!!!
    for (my $i=0; $i<scalar(@Ali)/2; $i++) {
	my $tmp = $Ali[$i];
	$Ali[$i] = $Ali[scalar(@Ali)-1-$i];
	$Ali[scalar(@Ali)-1-$i] = $tmp;
    }

    return \@Ali;
    
}







###############################################################
#
#  Function:  RecordFrameConflict
#
sub RecordFrameConflict
{
    my $fname = shift;
    
    my $target_species = shift;
    my $chr = shift;
    my $revcomp = shift;
    my $search_start = shift;
    my $search_end = shift;
    my $nucl_seq = shift;
    my $best_frame_num = shift;
    my $frame_trans_ref = shift;
    
    my @FrameTranslations = @{$frame_trans_ref};

    my $matched_ids_ref = shift;
    my $unmatched_ids_ref = shift;
    my $unmatched_frames_ref = shift;
    my $source_species_ref = shift;
    my $source_seqs_ref = shift;

    my @MatchedSourceIDs = @{$matched_ids_ref};
    my @UnmatchedSourceIDs = @{$unmatched_ids_ref};
    my @UnmatchedFramePrefs = @{$unmatched_frames_ref};
    my @SourceSpecies = @{$source_species_ref};
    my @SourceSeqs = @{$source_seqs_ref};

    my $file_exists = 0;
    if (-e $fname) {
	$file_exists = 1;
    }

    open(my $outf,'>>',$fname) || die "\n  ERROR: Failed to open output file '$fname'\n\n";

    if ($file_exists) {
	print $outf "===========================================================\n\n\n";
    }
    
    if ($revcomp) {
	$chr = $chr.'[revcomp]';
    }

    print $outf "Target Species : $target_species\n";
    print $outf "Search Range   : $chr:$search_start..$search_end\n";
    print $outf "Nucleotides    : ";
    my @Nucls = split(//,$nucl_seq);
    for (my $i=0; $i<scalar(@Nucls); $i++) {
	print $outf "$Nucls[$i]";
	if ($i+1 < scalar(@Nucls) && ($i+1) % 60 == 0) {
	    print $outf "\n                 ";
	}
    }
    print $outf "\n\n";

    print $outf "MSA Frame ($best_frame_num)  : ";
    my @Seq = split(//,$FrameTranslations[$best_frame_num]);
    for (my $i=0; $i<scalar(@Seq); $i++) {
	print $outf "$Seq[$i]";
	if ($i+1 < scalar(@Seq) && ($i+1) % 60 == 0) {
	    print $outf "\n                 ";
	}
    }
    print $outf "\n\n";

    foreach my $source_id (@MatchedSourceIDs) {
	print $outf "                 + $SourceSpecies[$source_id]\n";
    }
    print $outf "\n";
    
    my %PrefFramesToSpecies;
    my %SpeciesToIDs;
    for (my $i=0; $i<scalar(@UnmatchedFramePrefs); $i++) {
	my $pref_frame = $UnmatchedFramePrefs[$i];
	my $source_species = $SourceSpecies[$UnmatchedSourceIDs[$i]];
	$SpeciesToIDs{$source_species} = $i+1;
	if ($PrefFramesToSpecies{$pref_frame}) {
	    $PrefFramesToSpecies{$pref_frame} = $PrefFramesToSpecies{$pref_frame}.','.$source_species;
	} else {
	    $PrefFramesToSpecies{$pref_frame} = $source_species;
	}
    }

    for (my $frame=0; $frame<3; $frame++) {

	next if ($frame == $best_frame_num);

	print $outf "    Frame  $frame   : ";
	my @Seq = split(//,$FrameTranslations[$frame]);
	for (my $i=0; $i<scalar(@Seq); $i++) {
	    print $outf "$Seq[$i]";
	    if ($i+1 < scalar(@Seq) && ($i+1) % 60 == 0) {
		print $outf "\n                 ";
	    }
	}
	print $outf "\n\n";

	if (!$PrefFramesToSpecies{$frame}) {
	    print $outf "                 - Not preferred by any source species\n\n";
	    next;
	}

	foreach my $source_species (split(/\,/,$PrefFramesToSpecies{$frame})) {
	    my $source_id = $SpeciesToIDs{$source_species}-1;
	    print $outf "                 + $source_species\n";
	    print $outf "                   $SourceSeqs[$source_id]\n\n";
	}
	
    }
    
    print $outf "\n\n";
    close($outf);
    
}






###############################################################
#
#  Function:  GetMapSummaryStats
#
sub GetMapSummaryStats
{

    my $ghostlygenes_ref = shift;
    my @GhostlyGenes = @{$ghostlygenes_ref};

    my $outf = OpenOutputFile($outdirname.'Search-Summary.out');

    my %TargetSpeciesToSuggested;
    my %TargetSpeciesToAnnotated;
    my @FullHitList;
    
    foreach my $gene (sort @GhostlyGenes) {
	
	my $infname = $outgenesdir.$gene.'/search.out';
	my $inf = OpenInputFile($infname);
	
	print $outf "\n  $gene\n";
	
	# We'll want to know how many ranges had mappings for this gene
	# (e.g., distinct blocks in the MSA).
	my $num_mapped_ranges = 0;
	my %MapsByExonRange;
	while (my $line = <$inf>) {
	    
	    # The sure-fire sign of a good time!
	    if ($line =~ /\[\+\]/) {
		
		# Where in the MSA is this mapping from?
		$line = <$inf>;
		$line =~ /Exons? (\S+)/;
		my $exon_range = $1;
		
		# Which genome was being searched against?
		$line = <$inf>;
		$line =~ /\: (\S+) \((\S+)\)\s*$/;
		my $target_species = $1;
		my $target_region = $2;
		
		# Which species provided the protein sequence?
		$line = <$inf>;
		$line =~ /\: (\S+)/;
		my $source_species = $1;
		
		# What was the protein sequence we were searching with?
		# Note that mapped residues are uppercase, so we can
		#   compute the percentage of the search sequence that
		#   was mapped.
		$line = <$inf>;
		$line =~ /\: (\S+)/;
		my $num_mapped_chars = 0;
		my $num_unmapped_chars = 0;
		foreach my $char (split(//,$line)) {
		    if ($char =~ /[A-Z]/) { $num_mapped_chars++;   }
		    else                  { $num_unmapped_chars++; }
		}
		my $search_seq_len = $num_mapped_chars + $num_unmapped_chars;
		my $pct_seq_mapped = int(1000.0 * $num_mapped_chars / $search_seq_len) / 10.0;
		
		# tblastn hit count? (this plays into the final part of our hash val)
		$line = <$inf>;
		$line =~ /\: (\d+)/;
		my $num_hits = $1;
		
		# We'll store this data in a hash, which we can then sort by
		# MSA position (further broken down by target species).
		my $hash_val = $target_species.'|'.$target_region.'|'.$source_species;
		$hash_val = $hash_val.'|'.$search_seq_len.'|'.$pct_seq_mapped;
		
		# Add the list of hit regions, too
		for (my $i=0; $i<$num_hits; $i++) {
		    $line = <$inf>;
		    $line =~ /mapped to \S+ \S+\:(\d+\.\.\d+)/;
		    my $map_range = $1;
		    $hash_val = $hash_val.'|'.$map_range;
		}
		
		if ($MapsByExonRange{$exon_range}) {
		    $MapsByExonRange{$exon_range} = $MapsByExonRange{$exon_range}.'&'.$hash_val;
		} else {
		    $MapsByExonRange{$exon_range} = $hash_val;
		    $num_mapped_ranges++;
		}
		
	    }
	    
	}
	
	close($inf);
	
	# Print out the number of mapped ranges 
	print $outf "  $num_mapped_ranges exon range";
	print $outf "s" if ($num_mapped_ranges > 1);
	print $outf " in MSA produced ghost exon mappings\n";
	
	# We now have all the info. we could need to grab from the file,
	# so it's time to organize it!
	foreach my $exon_range (sort keys %MapsByExonRange) {
	    
	    my %MapsByTargetSpecies;
	    my $num_targets_in_range = 0;
	    foreach my $map_in_range (split(/\&/,$MapsByExonRange{$exon_range})) {

		$map_in_range =~ /^([^\|]+)\|/;
		my $species = $1;
		
		if ($MapsByTargetSpecies{$species}) {
		    $MapsByTargetSpecies{$species} = $MapsByTargetSpecies{$species}.'&'.$map_in_range;
		} else {
		    $MapsByTargetSpecies{$species} = $map_in_range;
		    $num_targets_in_range++;
		}
		
	    }
	    
	    # Announce this range
	    print $outf "\n    > MSA exon";
	    print $outf "s" if ($exon_range =~ /\.\./);
	    print $outf " $exon_range: Found mappings to $num_targets_in_range genome";
	    print $outf "s" if ($num_targets_in_range > 1);
	    print $outf "\n";
	    
	    # We can now consider searches within this exon range by order
	    # of target species.
	    foreach my $target_species (sort keys %MapsByTargetSpecies) {

		my @MapsToSpecies = split(/\&/,$MapsByTargetSpecies{$target_species});
		
		# We'll go ahead and grab the region of the target species' genome that
		# was mapped to (should be consistent...)
		$MapsToSpecies[0] =~ /^[^\|]+\|([^\|]+)\|/;
		my $target_species_region = $1;

		# Write to this species' .bed file roight quicke!
		open(my $TargetBed,'>>',$bedfilesdir.$target_species.'.bed');

		$target_species_region =~ /([^\:]+)\:(\d+)\.\.(\d+)/;
		my $chr = $1;
		my $start = $2;
		my $end = $3;

		my $strand = '+';
		if ($chr =~ /\[revcomp\]/) {
		    $chr =~ s/\[revcomp\]//;
		    my $tmp = $start;
		    $start = $end;
		    $end = $tmp;
		    $strand = '-';
		}
		
		my $bed_name = $gene.'-exon';
		$bed_name = $bed_name.'s' if ($exon_range =~ /\.\./);
		$bed_name = $bed_name.'_'.$exon_range;

		print $TargetBed "$chr $start $end $bed_name 0 $strand\n";
		close($TargetBed);

		# Bed time is over -- back to work!
		my $num_maps_to_species = scalar(@MapsToSpecies);
		
		# As is customary in this region, we must declare the number of mappings
		# made to this species' genome.
		print $outf "\n        $num_maps_to_species mapping";
		print $outf "s" if ($num_maps_to_species > 1);
		print $outf " to target species $target_species ($target_species_region)\n";
		
	    }
	    
	}
	
    }

    close($outf);

}






#################################################################
#
#  Function:  CollapseAndCountOverlaps
#
sub CollapseAndCountOverlaps
{
    my $range_list_ref = shift;
    my @RangeList = @{$range_list_ref};

    my $known_exon_ref = shift;
    my @KnownExon = @{$known_exon_ref};
    
    my @RangeStarts;
    my @RangeEnds;
    foreach my $range (@RangeList) {
	$range =~ /^(\d+)\.\.(\d+)$/;
	push(@RangeStarts,$1);
	push(@RangeEnds,$2);
    }
    
    my $num_ranges = scalar(@RangeList);
    
    # Because we're just identifying overlaps, we can swap things around
    # so that start < end (i.e., de-revcomp)
    if ($RangeStarts[0] > $RangeEnds[0]) {
	for (my $i=0; $i<$num_ranges; $i++) {
	    my $temp = $RangeStarts[$i];
	    $RangeStarts[$i] = $RangeEnds[$i];
	    $RangeEnds[$i] = $temp;
	}
    }
    
    my %StartsToEnds;
    my %StartsToKnownExons;
    for (my $i=0; $i<$num_ranges; $i++) {
	my $start = $RangeStarts[$i];
	my $end = $RangeEnds[$i];
	if (!$StartsToEnds{$start}
	    || ($StartsToEnds{$start} && $StartsToEnds{$start} < $end)) {
	    $StartsToEnds{$start} = $end;
	}
	if ($KnownExon[$i]) {
	    $StartsToKnownExons{$start} = 1;
	}
    }
    
    my @CollapsedStarts = sort { $a <=> $b } keys %StartsToEnds;
    my @CollapsedEnds;
    foreach my $start (@CollapsedStarts) {
	push(@CollapsedEnds,$StartsToEnds{$start});
    }

    my $num_known = 0;
    my $is_known = 0;
    $is_known = 1 if ($StartsToKnownExons{$CollapsedStarts[0]});
    my $num_exons = 1;
    my $current_end = $CollapsedEnds[0];
    for (my $i=1; $i<scalar(@CollapsedEnds); $i++) {
	if ($current_end < $CollapsedStarts[$i]) {
	    $num_exons++;
	    $num_known += $is_known;
	    $is_known = 0;
	}
	$is_known = 1 if ($StartsToKnownExons{$CollapsedStarts[$i]});
	$current_end = Max($current_end,$CollapsedEnds[$i]);
    }

    $num_known += $is_known;

    return ($num_exons,$num_known);
    
}







#################################################################
#
#  Function: CheckNovelty
#
sub CheckNovelty
{
    my $species  = shift;
    my $gtf_name = shift;

    my $GTF = OpenInputFile($gtf_name);
    while (my $line = <$GTF>) {

	next if ($line !~ /^\s*(\S+)\s+\S+(\S+)\s+(\d+)\s+(\d+)\s+\S+\s+(\S+)/);

	my $gtf_chr    = $1;
	my $gtf_type   = lc($2);
	my $gtf_start  = $3;
	my $gtf_end    = $4;
	my $gtf_strand = $5;

	if ($gtf_type ne 'cds' && $gtf_type ne 'exon') { next; }

	my $start_mb_range = int($gtf_start / 100000);
	my $end_mb_range   = int($gtf_end   / 100000);

	my $range_key_1 = $species.'/'.$gtf_chr.$gtf_strand.':'.$start_mb_range;
	my $range_key_2 = $species.'/'.$gtf_chr.$gtf_strand.':'.$end_mb_range;

	# DEBUGGING
	print "\n\n";
	print " RK1: $range_key_1\n";
	print " RK2: $range_key_2\n";
	print "\n\n";
	foreach my $hashkey (keys %SpeciesChrMbRangeToHits) {
	    print " ---> $hashkey\n";
	}
	die "\n\n";
	# DEBUGGING

	foreach my $thread_hit_id (split(/\|/,$SpeciesChrMbRangeToHits{$range_key_1})) {

	    next if ($ThreadHitNumToNovelty[$thread_hit_id] ne 'Novel');

	    $ThreadHitNumToFileAndData[$thread_hit_id] =~ /\:(\d+)\.\.(\d+)/;
	    my $hit_start = $1;
	    my $hit_end = $2;

	    if ($gtf_strand eq '-') {
		my $tmp = $hit_start;
		$hit_start = $hit_end;
		$hit_end = $tmp;
	    }

	    if (($hit_start <= $gtf_start && $hit_end >= $gtf_start)
		|| ($hit_start <= $gtf_end && $hit_end >= $gtf_end)
		|| ($hit_start >= $gtf_start && $hit_end <= $gtf_end)) {
		$ThreadHitNumToNovelty[$thread_hit_id] = ' GTF ';
	    }
	    
	}

	next if ($range_key_1 eq $range_key_2);
	
	foreach my $thread_hit_id (split(/\|/,$SpeciesChrMbRangeToHits{$range_key_2})) {

	    next if ($ThreadHitNumToNovelty[$thread_hit_id] ne 'Novel');

	    $ThreadHitNumToFileAndData[$thread_hit_id] =~ /\:(\d+)\.\.(\d+)/;
	    my $hit_start = $1;
	    my $hit_end = $2;

	    if ($gtf_strand eq '-') {
		my $tmp = $hit_start;
		$hit_start = $hit_end;
		$hit_end = $tmp;
	    }

	    if (($hit_start <= $gtf_start && $hit_end >= $gtf_start)
		|| ($hit_start <= $gtf_end && $hit_end >= $gtf_end)
		|| ($hit_start >= $gtf_start && $hit_end <= $gtf_end)) {
		$ThreadHitNumToNovelty[$thread_hit_id] = ' GTF ';
	    }
	    
	}

    }
    close($GTF);
    
}







#################################################################
#
#  Function:  RecordNovelty
#
sub RecordNovelty
{
    for (my $thread_hit_id=0; $thread_hit_id<$num_thread_hits; $thread_hit_id++) {

	$ThreadHitNumToFileAndData[$thread_hit_id] =~ /^(.*)\|([^\|]+)$/;

	my $fname = $1;
	my $target_line = $2;

	my $tmp_fname = $fname;
	$tmp_fname =~ s/\.out$/\.tmp/;

	open(my $Tmp,'>',$tmp_fname)
	    || die "\n  ERROR:  Failed to open temp file '$tmp_fname'\n\n";
	my $InFile = OpenInputFile($fname);

	my $line = <$InFile>;
	print $Tmp "$line";
	while ($line ne $target_line) {
	    $line = <$InFile>;
	    print $Tmp "$line";
	}

	print $Tmp "         : ";
	if ($ThreadHitNumToNovelty[$thread_hit_id] eq 'Novel') {
	    print $Tmp "Novel exon (no GTF overlaps)\n";
	} else {
	    print $Tmp "Overlaps with GTF entry\n";
	} 

	while (!eof($InFile)) {
	    $line = <$InFile>;
	    print $Tmp "$line";
	}
	
	close($InFile);
	close($Tmp);

	RunSystemCommand("mv \"$tmp_fname\" \"$fname\"");
	
    }
}






#################################################################
#
#  Function:  RecordHitsByPctID
#
sub RecordHitsByPctID
{
    
    my $genesdirname = ConfirmDirectory($outdirname.'Results-by-Gene');

    my $max_gene_len = 0;
    my $max_species_len = 0;
    my $max_ali_len = 0;
    my $max_chr_len = 0;

    # We'll gather some summary statistics to (potentially) output
    # at the very end of the script's execution
    my $total_hits = 0;
    my $total_non_gtf_hits = 0;
    my %TargetToHits;
    my %TargetToNonGTFHits;
    
    my $GenesDir = OpenDirectory($genesdirname);
    my %PctIDtoHits;
    while (my $gene = readdir($GenesDir)) {
	
	my $genealisdirname = ConfirmDirectory($genesdirname.$gene).'alignments/';
	next if (!(-d $genealisdirname));
	
	$gene =~ s/\/$//;
	
	if (length($gene) > $max_gene_len) {
	    $max_gene_len = length($gene);
	}
	
	my $AliDir = OpenDirectory($genealisdirname);
	while (my $ali = readdir($AliDir)) {
	    
	    next if ($ali !~ /^([^\.]+)\./);
	    my $target_species = $1;
	    
	    my $alifname = $genealisdirname.$ali;
	    my $alif = OpenInputFile($alifname);
	    
	    my $genome_coords;
	    my $is_novel_exon;
	    while (my $line = <$alif>) {
		
		if ($line =~ /Target \: \S+ (\S+)/) {
		    $genome_coords = $1;
		    next;
		}

		if ($line =~ /\: Novel exon/) {

		    $total_hits++;
		    if ($TargetToHits{$target_species}) { $TargetToHits{$target_species}++; }
		    else                                { $TargetToHits{$target_species}=1; }
		    
		    $total_non_gtf_hits++;
		    if ($TargetToNonGTFHits{$target_species}) { $TargetToNonGTFHits{$target_species}++; }
		    else                                      { $TargetToNonGTFHits{$target_species}=1; }
		    
		    $is_novel_exon=1;
		    next;

		}

		if ($line =~ /\: Overlaps/) {

		    $total_hits++;
		    if ($TargetToHits{$target_species}) { $TargetToHits{$target_species}++; }
		    else                                { $TargetToHits{$target_species}=1; }
		    
		    $is_novel_exon=0;
		    next;

		}
		
		if ($line =~ /\: (\S+) \/ aminos (\d+)\.\.(\d+) \S+ \/ (\S+)\% ali/) {
		    
		    my $source_species = $1;
		    my $ali_len = $3 - $2 + 1;
		    my $pct_id = $4;

		    my $hash_val = $gene.':'.$source_species.'>'.$target_species.'('.$genome_coords.'):'.$ali_len.'&'.$is_novel_exon;
		    
		    if ($PctIDtoHits{$pct_id}) {
			$PctIDtoHits{$pct_id} = $PctIDtoHits{$pct_id}.'|'.$hash_val;
		    } else {
			$PctIDtoHits{$pct_id} = $hash_val;
		    }
		    
		    if (length($source_species) > $max_species_len) {
			$max_species_len = length($source_species);
		    }
		    if (length($target_species) > $max_species_len) {
			$max_species_len = length($target_species);
		    }
		    if (length($genome_coords)+3 > $max_chr_len) {
			$max_chr_len = length($genome_coords)+3;
		    }
		    if (length($ali_len) > $max_ali_len) {
			$max_ali_len = length($ali_len);
		    }
		    
		}
		
	    }
	    close($alif);
	    
	}
	closedir($AliDir);
	
    }
    closedir($GenesDir);
    

    # At long last, we have all the data we need!  Now to just scream
    # about it!
    my $OutFile = OpenOutputFile($outdirname.'Hits-by-Pct-ID.out');

    foreach my $pct_id (sort {$b <=> $a} keys %PctIDtoHits) {
	
	my %HitsByLen;
	foreach my $hit (split(/\|/,$PctIDtoHits{$pct_id})) {
	    $hit =~ /\:(\d+)\&/;
	    my $len = $1;
	    if ($HitsByLen{$len}) {
		$HitsByLen{$len} = $HitsByLen{$len}.'|'.$hit;
	    } else {
		$HitsByLen{$len} = $hit;
	    }
	}
	
	my @OrderedHits;
	foreach my $len (sort {$b <=> $a} keys %HitsByLen) {
	    foreach my $hit (split(/\|/,$HitsByLen{$len})) {
		
		$hit =~ /^([^\&]+)\&(\d)$/;
		my $hit_str  = $1;
		my $is_novel = $2;

		$hit_str =~ /^([^\:]+)\:(\S+)\>(\S+)(\(\S+\))\:(\d+)/;
		my $gene = $1;
		my $source_species = $2;
		my $target_species = $3;
		my $target_chr = $4;
		my $ali_len = $5;
		
		while (length($gene) < $max_gene_len) {
		    $gene = $gene.' ';
		}
		while (length($source_species) < $max_species_len) {
		    $source_species = $source_species.' ';
		}
		while (length($target_species) < $max_species_len) {
		    $target_species = $target_species.' ';
		}
		while (length($target_chr) < $max_chr_len) {
		    $target_chr = $target_chr.' ';
		}
		while (length($ali_len) < $max_ali_len) {
		    $ali_len = ' '.$ali_len;
		}
		
		my $formatted_str;
		if ($is_novel) { $formatted_str = '[ Novel ] '; }
		else           { $formatted_str = '[  GTF  ] '; }
		$formatted_str = $formatted_str."$gene $source_species -> $target_species ";
		$formatted_str = $formatted_str."$target_chr $ali_len aminos";
		
		push(@OrderedHits,$formatted_str);
		
	    }
	}
	
	$pct_id = $pct_id.'%';
	while (length($pct_id) < 6) {
	    $pct_id = ' '.$pct_id;
	}
	
	for (my $i=0; $i<scalar(@OrderedHits); $i++) {
	    print $OutFile "$pct_id :$OrderedHits[$i]\n";
	}
	
    }

    
    # Don't go breakin' my heart, now  :'(
    if ($total_hits == 0) {
	return "\n  No novel coding regions uncovered\n\n";
    }


    # We have at least *some* hits to report!
    my $results_overview_str = "  Total number of exons uncovered by Diviner: $total_hits\n";
    foreach my $target_species (sort keys %TargetToHits) {
	$results_overview_str = $results_overview_str."    + $target_species: $TargetToHits{$target_species}\n";
    }
    $results_overview_str = $results_overview_str."\n";

    
    # Did we have any extra-novel (i.e., non-GTF overlapping) hits?
    if ($total_non_gtf_hits == 0) {

	$results_overview_str = $results_overview_str."  All uncovered exons overlap with GTF-annotated coding regions\n";
	
    } else {

	$results_overview_str = $results_overview_str."  Exons without overlapping GTF annotations:  $total_non_gtf_hits\n";
	foreach my $target_species (sort keys %TargetToNonGTFHits) {
	    $results_overview_str = $results_overview_str."    + $target_species: $TargetToNonGTFHits{$target_species}\n";
	}

    }

    # Told 'ya we'd return this string!
    return $results_overview_str;

}






# EOF
