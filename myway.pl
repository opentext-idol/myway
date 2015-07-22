#!/bin/sh
exec perl -wx $0 "$@"
if 0;
#!perl -w
#line 6

###############################################################################
# HP Autonomy
###############################################################################
#
# myway.pl
#
# A perl re-implementation of flyway, maintaining 100% compatibility with
# flyway schema files and tables whilst providing enhanced automatic operation
# and resilience.
#
###############################################################################

# FIXME: # {{{
#
# * Need to pre-filter restoration data, to fix the MySQL bug if logging is
#   enabled - see bugs.mysql.com/69970
#
# }}}

# TODO: # {{{
#
# * fork()/exec() pv when performing restorations, and check for failure.  If
#   so, show the last error from 'SHOW ENGINE INNODB STATUS';
#
# * Enhance Percona SQLParser code to handle more statement types;
#
# * Allow 'parse' dbdump option to tokenise backup?
#
# * Incorporate HPCS modules to allow backup directly to Object Store - this
#   requires splitting data into small (10MB) chunks and passing an overall
#   manifest on completion;
#
# * Make HPCS modules optional, so when not present myway.pl will still run,
#   but without Object Store functionality;
#
# * Check entry -> tokens -> tables -> db, and confirm it exists (caching seen
#   databases);
#
# * Add parser for GRANT, etc.;
#
# * Roll-back on failure - try to continue rather than dying?
#
# * Restore backups on failure;
#
# }}}

# Copyright 2014 Stuart Shelton, Autonomy Systems Ltd.
# Portions of this program are copyright 2010-2012 Percona Inc.
#
# Feedback and improvements are welcome.
#
# THIS PROGRAM IS PROVIDED "AS IS" AND WITHOUT ANY EXPRESS OR IMPLIED
# WARRANTIES, INCLUDING, WITHOUT LIMITATION, THE IMPLIED WARRANTIES OF
# MERCHANTIBILITY AND FITNESS FOR A PARTICULAR PURPOSE.
#
# This program is free software; you can redistribute it and/or modify it under
# the terms of the GNU General Public License as published by the Free Software
# Foundation, version 2; OR the Perl Artistic License.  On UNIX and similar
# systems, you can issue `man perlgpl' or `man perlartistic' to read these
# licenses.
#
# You should have received a copy of the GNU General Public License along with
# this program; if not, write to the Free Software Foundation, Inc., 59 Temple
# Place, Suite 330, Boston, MA  02111-1307  USA.

{
# Include Percona SQLParser # {{{

# ###########################################################################
# SQLParser package $Revision$
# ###########################################################################

# Package: SQLParser
# SQLParser parses common MySQL SQL statements into data structures.
# This parser is MySQL-specific and intentionally meant to handle only
# "common" cases.  Although there are many limiations (like UNION, CASE,
# etc.), many complex cases are handled that no other free, Perl SQL
# parser at the time of writing can parse, notably subqueries in all their
# places and varieties.
#
# This package has not been profiled and since it relies heavily on
# mildly complex regex, so do not expect amazing performance.
#
# See SQLParser.t for examples of the various data structures.  There are
# many and they vary a lot depending on the statment parsed, so documentation
# in this file is not exhaustive.
#
# This package differs from QueryParser because here we parse the entire SQL
# statement (thus giving access to all its parts), whereas QueryParser extracts
# just needed parts (and ignores all the rest).

package SQLParser;

use strict;
use warnings FATAL => 'all';

use English qw(-no_match_vars);

use constant MKDEBUG => $ENV{MKDEBUG} || 0;
use constant SQLDEBUG => $ENV{SQLDEBUG} || 0;

use constant DEFDELIM => ';';

# Used by improved parse_values
use Regexp::Common;

use Data::Dumper;
$Data::Dumper::Indent    = 1;
$Data::Dumper::Sortkeys  = 1;
$Data::Dumper::Quotekeys = 0;

sub new( $% );
sub parse( $$;$ );

sub parse_alter( $$ );
sub parse_call( $$ );
sub parse_create( $$ );
sub parse_delete( $$ );
sub parse_drop( $$ );
#sub parse_grant( $$ );
sub parse_insert( $$ ); # Alias of parse_replace
sub parse_select( $$ );
sub parse_update( $$ );

sub parse_add( $$ );
sub parse_change( $$ );
sub parse_character_set( $$ );
sub parse_columns( $$ );
sub parse_from( $$ ); # Alias of parse_into, parse_tables
sub parse_group_by( $$ );
sub parse_having( $$ );
sub parse_identifier( $$$ );
sub parse_identifiers( $$ );
sub parse_limit( $$ );
sub parse_modify( $$ );
sub parse_order_by( $$ );
sub parse_set( $$ );
sub parse_table_reference( $$ );
sub parse_values( $$ );
sub parse_where( $$ );

sub clean_query( $$ );
sub is_identifier( $$ );
sub normalize_keyword_spaces( $$ );
sub remove_functions( $$ );
sub remove_subqueries( $$ );
sub remove_using_columns( $$ );
sub replace_function( $$ );
sub set_Schema( $$ );
sub split_unquote( $$$ );
sub _parse_clauses( $$ );
sub _parse_csv( $$$ );
sub _parse_query( $$$$$ );
sub _is_constant( $$ );
sub _d;

# Basic identifers for database, table, column and function names.
my $quoted_ident   = qr/`[^`]+`/;
# '' is a valid constant...
#my $constant_ident   = qr/'[^']+'/;
my $constant_ident   = qr/'[^']*'/;
#my $unquoted_ident = qr/
#	\@{0,2}         # optional @ or @@ for variables
#	\w+             # the ident name
#	(?:\s*\([^\)]*\))? # optional function params
#/x;
my $unquoted_ident = qr/
	\@{0,2}         # optional @ or @@ for variables
	\w+             # the ident name
	(?:\s*$RE{ balanced }{ -parens => '()' })? # optional function params
/x;

my $ident_alias = qr/
  \s+                                 # space before alias
  (?:(AS)\s+)?                        # optional AS keyword
  ((?>$quoted_ident|$unquoted_ident)) # alais
/xi;

#my $function_ident = qr/
#	\s*
#	(
#		(?:\b\w+|`\w+`)\s*    # function name
#		\(                    # opening parenthesis
#		[^\)]*                # function args, if any
#		\)                    # closing parenthesis
#	)
#/x;
my $function_ident = qr/
	(
		(?:\b\w+|`\w+`)\s*    # function name
		$RE{ balanced }{ -parens => '()' }
	)
/x;

# A table is identified by 1 or 2 identifiers separated by a period
# and optionally followed by an alias.  See parse_table_reference()
# for why an optional index hint is not included here.
my $table_ident = qr/(?:
	((?:(?>$quoted_ident|$unquoted_ident)\.?){1,2}) # table
	(?:$ident_alias)?                               # optional alias
)/xo;

# A column is identified by 1 to 3 identifiers separated by periods
# and optionally followed by an alias.
my $column_ident = qr/(?:
	((?:(?>$quoted_ident|$constant_ident|$function_ident|$unquoted_ident|\*)\.?){1,3}) # column
	(?:$ident_alias)?                                  # optional alias
)/xo;

my %ignore_function = (
	IN    => 1,
	INDEX => 1,
	KEY   => 1,
);

# Sub: new # {{{
#   Create a SQLParser object.
#
# Parameters:
#   %args - Arguments
#
# Optional Arguments:
#   Schema - <Schema> object.  Can be set later by calling <set_Schema()>.
#
# Returns:
#   SQLParser object
sub new( $% ) {
	my ( $class, %args ) = @_;
	my $self = {
		  %args
		,  delimiter => DEFDELIM
	};
	return( bless( $self, $class ) );
} # new # }}}

# Sub: parse # {{{
#   Parse a SQL statment.   Only statements of $allowed_types are parsed.
#   This sub recurses to parse subqueries.
#
# Parameters:
#   $query - SQL statement
#
# Returns:
#   A complex hashref of the parsed SQL statment.  All keys and almost all
#   values are lowercase for consistency.  The struct is roughly:
#   (start code)
#   {
#     type       => '',     # one of $allowed_types
#     clauses    => {},     # raw, unparsed text of clauses
#     <clause>   => struct  # parsed clause struct, e.g. from => [<tables>]
#     keywords   => {},     # LOW_PRIORITY, DISTINCT, SQL_CACHE, etc.
#     functions  => {},     # MAX(), SUM(), NOW(), etc.
#     select     => {},     # SELECT struct for INSERT/REPLACE ... SELECT
#     subqueries => [],     # pointers to subquery structs
#   }
#   (end code)
#   It varies, of course, depending on the query.  If something is missing
#   it means the query doesn't have that part.  E.g. INSERT has an INTO clause
#   but DELETE does not, and only DELETE and SELECT have FROM clauses.  Each
#   clause struct is different; see their respective parse_CLAUSE subs.
sub parse( $$;$ ) {
	my ( $self, $query, $delim ) = @_;
	return unless $query;

	$delim = DEFDELIM unless( defined( $delim ) and length( $delim ) );

	#MKDEBUG && _d('Query:', $query);

	# Only these types of statements are parsed.
	my $allowed_types = qr/(?:
		 ALTER
		|CALL
		|CREATE
		|DELETE
		|DELIMITER
		|DROP
		|INSERT
		|REPLACE
		|SELECT
		|UPDATE
	)/xi;
		#|GRANT

	# Flatten and clean query.
	$query = $self->clean_query($query);

	# Remove first word, should be the statement type.  The parse_TYPE subs
	# expect that this is already removed.
	my $type;
	if ( $query =~ s/^(\w+)\s+// ) {
		$type = lc $1;
		MKDEBUG && _d('Query type:', $type);
		die "Cannot parse " . uc($type) . " queries"
			unless $type =~ m/$allowed_types/i;
	}
	elsif( $query eq $delim ) {
		# This is a bit of a hack to catch fragments after hints which
		# may have been passed through this far...
		return( undef );
	}
	else {
		die "Query '$query' does not begin with a word";  # shouldn't happen
	}

	$query = $self->normalize_keyword_spaces($query);

	MKDEBUG && _d('Normalised query:', $type, $query);

	if ( 'delimiter' eq $type ) {
		my @terms = split( /\s+/, $query );
		$self->{delimiter} = shift( @terms );
		my $struct;
		$struct->{type} = $type;
		$struct->{delimiter} = $self->{delimiter};
		$struct->{unknown} = join( ' ', @terms );
		return $struct;
	}

	# If query has any subqueries, remove/save them and replace them.
	# They'll be parsed later, after the main outer query.
	my @subqueries;
	if ( $query =~ m/(\(\s*SELECT\s+)/i ) {
		MKDEBUG && _d('Removing subqueries');
		@subqueries = $self->remove_subqueries($query);
		$query      = shift @subqueries;
	}
	elsif ( $type eq 'create' && $query =~ m/\s+SELECT/ ) {
		# XXX: create PROCEDURE may contain SELECT sub-queries, but
		#      it cannot be assumed that they will continue to the end
		#      of the line.  Delimiter-parsing in this instance is not
		#      trivial, as the active delimiter may differ from ';',
		#      which may also appear (without delimiting) in a quoted
		#      string...
		MKDEBUG && _d('CREATE..SELECT');
		#($subqueries[0]->{query}) = $query =~ m/\s+(SELECT\s+.+)/;
		#$query =~ s/\s+SELECT\s+.+//;
		# XXX: Let's give is a try anyway...
		($subqueries[0]->{query}) = $query =~ m/\s+(SELECT\s+[^;]+)/;
		$query =~ s/\s+SELECT\s+[^;]+//;
	}

	# Parse raw text parts from query.  The parse_TYPE subs only do half
	# the work: parsing raw text parts of clauses, tables, functions, etc.
	# Since these parts are invariant (e.g. a LIMIT clause is same for any
	# type of SQL statement) they are parsed later via other parse_CLAUSE
	# subs, instead of parsing them individually in each parse_TYPE sub.
	my $parse_func = "parse_$type";
	my $struct     = $self->$parse_func($query);
	if ( !$struct ) {
		MKDEBUG && _d($parse_func, 'failed to parse query');
		return;
	}
	$struct->{type} = $type;
	$self->_parse_clauses($struct);
	# TODO: parse functions

	if ( @subqueries ) {
		MKDEBUG && _d('Parsing subqueries');
		foreach my $subquery ( @subqueries ) {
			my $subquery_struct = $self->parse($subquery->{query});
			@{$subquery_struct}{keys %$subquery} = values %$subquery;
			push @{$struct->{subqueries}}, $subquery_struct;
		}
	}

	MKDEBUG && _d('Query struct:', Dumper($struct));
	return $struct;
} # parse # }}}

# Functions to handle top-level SQL elements

sub parse_alter( $$ ) { # {{{
	my ( $self, $query ) = @_;

	my $keywords = qr/(ONLINE|OFFLINE|IGNORE)/i;
	my ( $type, @query ) = split( /\s+/, $query );
	$query = join( ' ', @query );

	if( $type =~ m/TABLE/i ) {
		$query =~ s/^\s*TABLE\s+//i;

		#my $clauses = qr/(ADD(?:\s+(?:COLUMN|INDEX|KEY|CONSTRAINT|(?:CONSTRAINT\s+)?(?:(?:PRIMARY|FOREIGN)\s+KEY|UNIQUE\s+(?:INDEX|KEY))|(?:FULLTEXT|SPATIAL)\s+(?:INDEX|KEY)))?|(?:ALTER|CHANGE|MODIFY)(?:\s+COLUMN)?|DROP(?:\s+(?:COLUMN|INDEX|(?:(?:PRIMARY|FOREIGN)\s+)?KEY))?|(?:DIS|EN)ABLE\s+KEYS|RENAME\s+(?:TO|AS)?|ORDER\s+BY|CONVERT\s+TO\s+CHARACTER\s+SET|(?:DEFAULT\s+)?CHARACTER\s+SET(?:\s+=)?|(?:DISCARD|IMPORT)\s+TABLESPACE|(?:ADD|DROP|COALESCE|REORGANISE|ANALYSE|CHECK|OPTIMIZE|REBUILD|REPAIR)\s+PARTITION|PARTITION\s+BY|REMOVE\s+PARTITIONING)/i;
		my $clauses = qr/(ADD|(?:ALTER|CHANGE|MODIFY)|DROP|(?:DIS|EN)ABLE\s+KEYS|RENAME|ORDER\s+BY|CONVERT\s+TO\s+CHARACTER\s+SET|(?:DEFAULT\s+)?CHARACTER\s+SET|(?:DISCARD|IMPORT)\s+TABLESPACE|(?:ADD|DROP|COALESCE|REORGANISE|ANALYSE|CHECK|OPTIMIZE|REBUILD|REPAIR)\s+PARTITION|PARTITION\s+BY|REMOVE\s+PARTITIONING)/i;
		return $self->_parse_query($query, $keywords, 'tables', $clauses);

	}
} # parse_alter # }}}

sub parse_call( $$ ) { # {{{
	my ($self, $query) = @_;
	my ($name) = $query =~ m/
		(\S+)(?:\s*\(.*\)\s*)?
	/xi;
	$name =~ s/['"]//g;
	$name =~ s/\(\s*\)$//;
	return {
		object  => 'procedure',
		name    => $name,
		unknown => undef,
	};
} # parse_call # }}}

sub parse_create( $$ ) { # {{{
	my ($self, $query) = @_;
	return unless $query;

	# FIXME: This function will only really parse 'CREATE TABLE', and even
	#        then it doesn't give much information :(

	my ($obj, $name) = $query =~ m/
		(\S+)\s+
		(?:IF\s+NOT\s+EXISTS\s+)?
		(\S+)\s*.*$
	/xi;
	$name =~ s/['"]//g;
	$name =~ s/\(\s*\)$//;
	$name =~ s/[;(]$//;
	my $struct = {
		object  => lc $obj,
		name    => $name,
		unknown => undef,
	};

	if( lc( $obj ) eq 'procedure' ) {
		$query =~ s/\sBEGIN\s/ BEGIN; /gi;
		$query =~ s/\sEND( IF)\s/ END$1; /gi;
		$query =~ s/\sTHEN\s/ THEN; /gi;
		MKDEBUG && _d('Filtered query:', $query);
		my @subqueries = split( /;/, DEFDELIM . $query . DEFDELIM );
		for( my $n = 0 ; $n < scalar( @subqueries ) ; $n++ ) {
			my $subquery = $subqueries[ $n ];
			if( 0 == $n ) {
				$subquery = '';
			} elsif( 1 == $n ) {
				$subquery =~ s/^.*?BEGIN//;
				MKDEBUG && _d('Filtered initial sub-query:', $subquery);
			} elsif( scalar( @subqueries ) - 1 == $n ) {
				$subquery =~ s/END.*?$//;
				MKDEBUG && _d('Filtered final sub-query:', $subquery);
			}
			$subquery =~ s/^\s+//;
			$subquery =~ s/\s+$//;
			if( length( $subquery ) ) {
				MKDEBUG && _d('Parsing CREATE PROCEDURE sub-query:', $subquery);
				my $subquery_struct;
				eval {
					$subquery_struct = $self->parse($subquery);
				};
				if( $@ ) {
					$subquery_struct = { unknown => $subquery };
				}
				push @{$struct->{subqueries}}, $subquery_struct;
			}
		}
	}

	MKDEBUG && _d('Create struct:', Dumper($struct));
	return $struct;
} # parse_create # }}}

sub parse_delete( $$ ) { # {{{
	my ( $self, $query ) = @_;
	if ( $query =~ s/FROM\s+//i ) {
		my $keywords = qr/(LOW_PRIORITY|QUICK|IGNORE)/i;
		my $clauses  = qr/(FROM|WHERE|ORDER\s+BY|LIMIT(?:\s+\d+))/i;
		return $self->_parse_query($query, $keywords, 'from', $clauses);
	}
	else {
		die "DELETE without FROM: $query";
	}
} # parse_delete # }}}

sub parse_drop( $$ ) { # {{{
	my ($self, $query) = @_;

	# Keywords are expected to be at the start of the query, so these
	# that appear at the end are handled separately.  Afaik, SELECT are
	# the only statements with optional keywords at the end.  These
	# also appear to be the only keywords with spaces instead of _.
	my @keywords;
	my $final_keywords = qr/(RESTRICT|CASCADE)/i;
	1 while $query =~ s/\s+$final_keywords/(push @keywords, $1), ''/gie;

	my $struct;

	my $delimiter = $self->{delimiter};
	$delimiter = DEFDELIM unless( defined( $delimiter ) and length( $delimiter ) );
	( my $terms = $query ) =~ s/\s*\Q$delimiter\E\s*$//;
	#( my $terms = $query ) =~ s/\s*$delimiter\s*$//;
	$terms =~ s/IF\s+EXISTS//;

	my( $type, @objects ) = split( /\s+/, $terms );
	if( $type =~ m/TEMPORARY/i ) {
		if( not( shift( @objects ) =~ m/TABLE/i ) ) {
			die "TEMPORARY without TABLE: $query";
		} else {
			$struct->{keywords}->{temporary} = 1;
			$type = 'TABLE';
		}
	}
	if( 'LOGFILE' eq uc( $type ) ) {
		$type .= ' ' . shift( @objects );
		if( not( 'LOGFILE GROUP' eq $type ) ) {
			die "LOGFILE without GROUP: $query";
		}
	}

	$struct->{object}  = lc( $type );

	if( uc( $type ) =~ m/DATABASE|EVENT|FUNCTION|PROCEDURE|SERVER|TRIGGER/ ) {
		if( scalar( @objects ) > 1 ) {
			die "DROP " . uc( $type ) . " supports only one parameter: $query";
		}
		$struct->{name} = shift( @objects );

	} elsif( uc( $type ) eq 'INDEX' ) {
		# Handle 'ON tbl_name' plus optional 'ALGORITHM [=] {DEFAULT|INPLACE|COPY} | LOCK [=] {DEFAULT|NONE|SHARED|EXCLUSIVE} ...'
		my $name = shift( @objects );

		# XXX: Statements of the form:
		#          ALTER TABLE `foo` DROP INDEX `bar`
		#      ... will now invoke this code-path, so DROP without ON
		#      is valid iff we're part of an ALTER query. Unfortunately
		#      there's no way to tell whether this is the case at this.
		#
		if( scalar( @objects ) and not( 'ON' eq shift( @objects ) ) ) {
			die "DROP " . uc( $type ) . " without ON: $query";
		}

		my $tbl = shift( @objects );
		$struct->{name} = $self->parse_identifier('column', $name);
		$struct->{tbl} = $self->parse_identifier('table', $tbl) if( defined( $tbl ) );

		while( scalar( @objects ) ) {
			my $term = shift( @objects );
			if( not( $term =~ m/ALGORITHM|LOCK/i ) ) {
				die "DROP " . uc( $type ) . " unrecognised parameter $term: $query";
			}
			my $argument = shift( @objects );
			if( defined( $argument ) and ( '=' eq $argument ) ) {
				$argument = shift( @objects );
			}
			if( defined( $argument ) ) {
				$struct->{keywords}->{ lc( $term ) } = $argument;
			} else {
				die "Parameter $term requires an argument: $query";
			}
		}

	} elsif( uc( $type ) =~ m/LOGFILE GROUP|TABLESPACE/ ) {
		# Handle optional 'ENGINE [=] engine_name'
		$struct->{name} = shift( @objects );

		while( scalar( @objects ) ) {
			my $term = shift( @objects );
			if( not( $term =~ m/ENGINE/i ) ) {
				die "DROP " . uc( $type ) . " unrecognised parameter $term: $query";
			}
			my $argument = shift( @objects );
			if( defined( $argument ) and ( '=' eq $argument ) ) {
				$argument = shift( @objects );
			}
			if( defined( $argument ) ) {
				$struct->{keywords}->{ lc( $term ) } = $argument;
			} else {
				die "Parameter $term requires an argument: $query";
			}
		}

	} else {
		if( 1 == scalar( @objects ) ) {
			$struct->{name} = shift( @objects );
		} else {
			# TODO: Are commas in quoted object names valid?
			my $names = split( /,\s+/, join( ' ', @objects ) );
			$struct->{name} = $names;
		}
	}

	$struct->{unknown} = undef;

	# Add final keywords, if any.
	map { s/ /_/g; $struct->{keywords}->{lc $_} = 1; } @keywords;

	return $struct;
} # parse_drop # }}}

#sub parse_grant( $$ ) { # {{{
#	my ($self, $query) = @_;
#
#	my $keywords = qr/(
#		 ALL
#		|ALL\s+PRIVILEGES
#		|ALTER
#		|ALTER\s+ROUTINE
#		|CREATE
#		|CREATE\s+ROUTINE
#		|CREATE\s+TEMPORARY\s+TABLES
#		|CREATE\s+USER
#		|CREATE\s+VIEW
#		|DELETE
#		|DROP
#		|EVENT
#		|EXECUTE
#		|FILE
#		|GRANT\s+OPTION
#		|INDEX
#		|INSERT
#		|LOCK\s+TABLES
#		|PROCESS
#		|REFERENCES
#		|RELOAD
#		|RECPLICATION\s+CLIENT
#		|REPLICATION\s+SLAVE
#		|SELECT
#		|SHOW\s+DATABASES
#		|SHOW\s+VIEW
#		|SHUTDOWN
#		|SUPER
#		|TRIGGER
#		|UPDATE
#		|USAGE
#	)/xi;
#	my $clauses  = qr/(ON|TO|REQUIRE|AND|WITH)/i;
#
#	return $self->_parse_query($query, $keywords, 'grants', $clauses);
#} # parse_grant # }}}

sub parse_insert( $$ ) { # {{{
	my ( $self, $query ) = @_;
	return unless $query;

	MKDEBUG && _d('Parsing INSERT/REPLACE', $query);

	my $struct = {};

	my $delimiter = $self->{delimiter};
	$delimiter = DEFDELIM unless( defined( $delimiter ) and length( $delimiter ) );
	$query =~ s/\s*\Q$delimiter\E\s*$//;
	#$query =~ s/\s*$delimiter\s*$//;

	# Save, remove keywords.
	my $keywords   = qr/(LOW_PRIORITY|DELAYED|HIGH_PRIORITY|IGNORE)/i;
	1 while $query =~ s/$keywords\s+/$struct->{keywords}->{lc $1}=1, ''/gie;

	if ( $query =~ m/ON DUPLICATE KEY UPDATE (.+)/i ) {
		my $values = $1;
		die "No values after ON DUPLICATE KEY UPDATE: $query" unless $values;
		$struct->{clauses}->{on_duplicate} = $values;
		MKDEBUG && _d('Clause: on duplicate key update', $values);

		# This clause can be confused for JOIN ... ON in INSERT-SELECT queries,
		# so we remove the ON DUPLICATE KEY UPDATE clause after extracting its
		# values.
		$query =~ s/\s+ON DUPLICATE KEY UPDATE.+//;
	}

	# Parse INTO clause.  Literal "INTO" is optional.
#	if ( my @into = ($query =~ m/
#				(?:INTO\s+)?            # INTO, optional
#				(`[^`]+`|[^\s(]+?)\s*   # table ref
#				(\([^)]+\)\s+)?         # column list, optional
#				(VALUES?|SET|SELECT)\s* # start of next caluse
#			/xgci)
#	) {

	( my $string = $query ) =~ s/^\s*INTO\s+//;

	my $tbl;
	if( $string =~ m/^\s*`([^`]+)`/ and defined( $1 ) and length( $1 ) ) {
		$tbl = $1;
		MKDEBUG && _d('Found quoted table name', $tbl);
		$string =~ s/^\s*`\Q$tbl\E`\s*//;
	} elsif( $string =~ m/^\s*([^\s(]+?)[\s(]/ and defined( $1 ) and length( $1 ) ) {
		$tbl = $1;
		MKDEBUG && _d('Found table name', $tbl);
		$string =~ s/^\s*\Q$tbl\E\s*//;
	} else {
		die "INSERT/REPLACE without table: $query";
	}
	$struct->{clauses}->{into} = $tbl;
	MKDEBUG && _d('Clause: into', $tbl, ', string', $string);

	if( $string =~ m/^\s*(\(.*\))\s+(?:VALUES?|SET|SELECT)\s*/ ) {
		my @input = split( //, $1 );
		my @output;
		my $escaped = 0;
		my $quoted = 0;
		my $bra = 0;
		my $ket = 0;

		EXTRACT: foreach my $character ( @input ) {
			push( @output, $character );

			if( $character eq ')' and not( $quoted ) and ( $ket <= $bra ) ) {
				last EXTRACT;
			} else {
				if( $character eq "'" ) {
					if( not( $escaped ) ) {
						$quoted = not( $quoted );
					}
				} elsif( $character eq '(' ) {
					$bra++;
				} elsif( $character eq ')' ) {
					$ket++;
				}
				if( $character eq '\\' ) {
					$escaped = 1;
				} else {
					$escaped = 0;
				}
			}
		}
		my $cols = join( '', @output );
		$cols =~ s/^\(//;
		$cols =~ s/\)$//;
		if ( $cols ) {
			$struct->{clauses}->{columns} = $cols;
			MKDEBUG && _d('Clause: columns', $cols);

			$string =~ s/^\s*\(\s*\Q$cols\E\s*\)\s*//;
			#$string =~ s/^\s*\(\s*$cols\s*\)\s*//;
		} else {
			# Insert into no columns!?
			# Can apparently be used to create a new ID in an
			# auto-increment column of a table...
			$string =~ s/^\s*\(\s*\)\s*//;
		}
	}

	my @components = split( /\s+/, $string );
	my $next_clause = lc( shift( @components ) );  # VALUES, SET or SELECT
	die "INSERT/REPLACE without clause after table: $query"
		unless $next_clause;
	$next_clause = 'values' if $next_clause eq 'value';
	my ($values) = ($string =~ m/^\s*\Q$next_clause\E\s*(.*)$/i);
	#my ($values) = ($string =~ m/^\s*$next_clause\s*(.*)$/i);
	die "INSERT/REPLACE without values: $query" unless $values;
	$struct->{clauses}->{$next_clause} = $values;
	MKDEBUG && _d('Clause:', $next_clause, $values);

	# Save any leftovers.  If there are any, parsing missed something.
	($struct->{unknown}) = ($string =~ m/^\s*\Q$next_clause\E\s*\Q$values\E\s*(.*)$/i);
	#($struct->{unknown}) = ($string =~ m/^\s*\Q$next_clause\E\s*$values\s*(.*)$/i);
	#($struct->{unknown}) = ($string =~ m/^\s*$next_clause\s*$values\s*(.*)$/i);

#	if ( my @into = ($query =~ m/
#				(?:INTO\s+)?            # INTO, optional
#				(.+?)\s+                # table ref
#				(\([^\)]+\)\s+)?        # column list, optional
#				(VALUE.?|SET|SELECT)\s+ # start of next caluse
#			/xgci)
#	) {
#		my $tbl  = shift @into;  # table ref
#		$struct->{clauses}->{into} = $tbl;
#		MKDEBUG && _d('Clause: into', $tbl);
#
#		my $cols = shift @into;  # columns, maybe
#		if ( $cols ) {
#			$cols =~ s/[\(\)]//g;
#			$struct->{clauses}->{columns} = $cols;
#			MKDEBUG && _d('Clause: columns', $cols);
#		}
#
#		my $next_clause = lc(shift @into);  # VALUES, SET or SELECT
#		die "INSERT/REPLACE without clause after table: $query"
#			unless $next_clause;
#		$next_clause = 'values' if $next_clause eq 'value';
#		my ($values) = ($query =~ m/\G(.+)/gci);
#		die "INSERT/REPLACE without values: $query" unless $values;
#		$struct->{clauses}->{$next_clause} = $values;
#		MKDEBUG && _d('Clause:', $next_clause, $values);
#	}
#
#	# Save any leftovers.  If there are any, parsing missed something.
#	($struct->{unknown}) = ($query =~ m/\G(.+)/);

	return $struct;
} # parse_insert
{
	# Suppress warnings like "Name "SQLParser::parse_set" used only once:
	# possible typo at SQLParser.pm line 480." caused by the fact that we
	# don't call these aliases directly, they're called indirectly using
	# $parse_func, hence Perl can't see their being called a compile time.
	no warnings;
	# INSERT and REPLACE are so similar that they are both parsed
	# in parse_insert().
	*parse_replace = \&parse_insert;
} # }}}

sub parse_select( $$ ) { # {{{
	my ( $self, $query ) = @_;

	# Keywords are expected to be at the start of the query, so these
	# that appear at the end are handled separately.  Afaik, SELECT are
	# the only statements with optional keywords at the end.  These
	# also appear to be the only keywords with spaces instead of _.
	my @keywords;
	my $final_keywords = qr/(FOR\s+UPDATE|LOCK\s+IN\s+SHARE\s+MODE)/i;
	1 while $query =~ s/\s+$final_keywords/(push @keywords, $1), ''/gie;

	my $keywords = qr/(
		 ALL
		|DISTINCT
		|DISTINCTROW
		|HIGH_PRIORITY
		|STRAIGHT_JOIN
		|SQL_SMALL_RESULT
		|SQL_BIG_RESULT
		|SQL_BUFFER_RESULT
		|SQL_CACHE
		|SQL_NO_CACHE
		|SQL_CALC_FOUND_ROWS
	)/xi;
	my $clauses = qr/(
		 FROM
		|WHERE
		|GROUP\s+BY
		|HAVING
		|ORDER\s+BY
		|LIMIT(?:\s+\d+)
		|PROCEDURE
		|INTO\s+OUTFILE
	)/xi;
	my $struct = $self->_parse_query($query, $keywords, 'columns', $clauses);

	# Add final keywords, if any.
	map { s/ /_/g; $struct->{keywords}->{lc $_} = 1; } @keywords;

	return $struct;
} # parse_select # }}}

sub parse_update( $$ ) { # {{{
	my ( $self, $query ) = @_;

	my $keywords = qr/(LOW_PRIORITY|IGNORE)/i;
	my $clauses  = qr/(SET|WHERE|ORDER\s+BY|LIMIT(?:\s+\d+))/i;

	return $self->_parse_query($query, $keywords, 'tables', $clauses);
} # parse_update # }}}

# Functions to handle SQL components

# Sub: parse_add # {{{
# GROUP BY {col_name | expr | position} [ASC | DESC], ... [WITH ROLLUP]
sub parse_add( $$ ) {
	my ( $self, $add ) = @_;
	return unless $add;
	MKDEBUG && _d('Parsing ADD', $add);

	# Parse the identifers.
	my $idents = $self->parse_identifiers( $self->_parse_csv($add) );

	return $idents;
} # parse_add # }}}

sub parse_change( $$ ) { # {{{
	my ( $self, $change ) = @_;
	# TODO
	return $change;
} # parse_change # }}}

sub parse_character_set( $$ ) { # {{{
	my ( $self, $character_set ) = @_;
	# TODO
	return $character_set;
} # parse_character_set # }}}

sub parse_columns( $$ ) { # {{{
	my ( $self, $cols ) = @_;
	MKDEBUG && _d('Parsing columns list:', $cols);

	my @cols;
	pos $cols = 0;
	while (pos $cols < length $cols) {
MKDEBUG && _d("At position '" . ( ( pos $cols ) or 0 ) . "' of ", length $cols);
		if ($cols =~ m/\G\s*(__SQ\d+__)\s*(?>,|\Z)/gcxo) {
warn "SQL DEBUG: (4) " .
	( defined( $1 ) ? "\$1(db_tbl_col) is '$1'" : '' ) .
	( defined( $2 ) ? ", \$2(unused) is '$2'" : '' ) .
	( defined( $3 ) ? ", \$3(unused) is '$3'" : '' ) .
	( defined( $4 ) ? ", \$4(unused) is '$4'" : '' ) .
	( defined( $5 ) ? ", \$4(unused) is '$5'" : '' ) .
	"." if SQLDEBUG;
			MKDEBUG && _d("Passing-through expression with compressed element \"$1\"");
			my $col_struct = { expr => $1, (), () };
			push @cols, $col_struct;
		}
		# XXX: Looking at it, the alias/col/tbl hash is lacking either
		#      the col(umn) or the alias name, because only three
		#      values are stored :(
		# We see:
		# jobs.id AS id -> { alias => 'AS', col => 'id', tbl => 'jobs' }
		# ... so explicit_alias is missing, and $2 is in $3.
		#
		elsif ($cols =~ m/\G\s*($RE{ balanced }{ -parens => '()' })\s*(?>,|\Z)/gcxo) {
			my ($select_expr) = $1;
warn "SQL DEBUG: (5) " .
	( defined( $1 ) ? "\$1(db_tbl_col) is '$1'" : '' ) .
	( defined( $2 ) ? ", \$2(unused) is '$2'" : '' ) .
	( defined( $3 ) ? ", \$3(unused) is '$3'" : '' ) .
	( defined( $4 ) ? ", \$4(unused) is '$4'" : '' ) .
	( defined( $5 ) ? ", \$4(unused) is '$5'" : '' ) .
	"." if SQLDEBUG;
			# See comments for $function_ident(2) below
			MKDEBUG && _d("Cannot fully parse expression \"$select_expr\"");
			my $col_struct = { expr => $select_expr, (), () };
			push @cols, $col_struct;
		}
		elsif ($cols =~ m/\G\s*$column_ident\s*(?>,|\Z)/gcxo) {
warn "SQL DEBUG: (1) " .
	( defined( $1 ) ? "\$1(db_tbl_col) is '$1'" : '' ) .
	( defined( $2 ) ? ", \$2(unused) is '$2'" : '' ) .
	( defined( $3 ) ? ", \$3(as) is '$3'" : '' ) .
	( defined( $4 ) ? ", \$4(alias) is '$4'" : '' ) .
	( defined( $5 ) ? ", \$4(unused) is '$5'" : '' ) .
	"." if SQLDEBUG;
			#my ($db_tbl_col, $as, $alias) = ($1, $2, $3); # XXX
			my ($db_tbl_col, $as, $alias) = ($1, $3, $4); # XXX
			#MKDEBUG && _d("column identifier:", Dumper(\$db_tbl_col));
			my $ident_struct = $self->parse_identifier('column', $db_tbl_col);
			#MKDEBUG && _d("resulting column identifier struct:", Dumper(\$ident_struct));
			if (defined $ident_struct) {
				$alias =~ s/`//g if defined $alias and length $alias;
				my $col_struct = {
					%$ident_struct,
					($as    ? (explicit_alias => 1)      : ()),
					($alias ? (alias          => $alias) : ()),
				};
				push @cols, $col_struct;
			}
		}
		# Furthermore, if the LHS of a SELECT statement is actually a
		# function-call rather than an alias at all, then we need to
		# handle that differently (but only if the other approaches
		# have failed to match)...
		# Update: Moved to position 2
		elsif ($cols =~ m/\G\s*$function_ident\s*(?>,|\Z)/gcxo) {
			my ($select_expr) = $1;
warn "SQL DEBUG: (2) " .
	( defined( $1 ) ? "\$1(db_tbl_col) is '$1'" : '' ) .
	( defined( $2 ) ? ", \$2(as) is '$2'" : '' ) .
	( defined( $3 ) ? ", \$3(alias) is '$3'" : '' ) .
	( defined( $4 ) ? ", \$4(unused) is '$4'" : '' ) .
	( defined( $5 ) ? ", \$4(unused) is '$5'" : '' ) .
	"." if SQLDEBUG;
			# There's no obvious way to represent this in the
			# current structure, which is predecated upon having a
			# concrete identifier as a root element.  Having said
			# this, the expression is still represented in
			# { 'clauses' } -> { 'columns' } (although not as an
			# alias/col/tbl hash) so perhaps this is okay...
			MKDEBUG && _d("Cannot fully parse expression \"$select_expr\"");
			my $col_struct = { expr => $select_expr, (), () };
			push @cols, $col_struct;
		}
		# This can occur when, for example, the LHS of a SELECT
		# statement's alias definition is an expression rather
		# than a simple column-reference...
		elsif ($cols =~ m/\G\s*(.+?)$ident_alias\s*(?>,|\Z)/gcxo) {
			my ($select_expr, $as, $alias) = ($1, $2, $3); # XXX
warn "SQL DEBUG: (3) " .
	( defined( $1 ) ? "\$1(db_tbl_col) is '$1'" : '' ) .
	( defined( $2 ) ? ", \$2(as) is '$2'" : '' ) .
	( defined( $3 ) ? ", \$3(alias) is '$3'" : '' ) .
	( defined( $4 ) ? ", \$4(unused) is '$4'" : '' ) .
	( defined( $5 ) ? ", \$4(unused) is '$5'" : '' ) .
	"." if SQLDEBUG;
			$alias =~ s/`//g if $alias;
			# There's no obvious way to represent this in the
			# current structure, which is predecated upon having a
			# concrete identifier as a root element.  Having said
			# this, the expression is still represented in
			# { 'clauses' } -> { 'columns' } (although not as an
			# alias/col/tbl hash) so perhaps this is okay...
			MKDEBUG && _d("Cannot fully parse expression \"" . $select_expr . ( defined( $as ) ? ' ' . $as . ' ' : ' ' ) . $alias . "\"");
			my $col_struct = {
				expr => $select_expr,
				($as    ? (explicit_alias => 1)      : ()),
				($alias ? (alias          => $alias) : ()),
			};
			push @cols, $col_struct;
		}
		elsif ($cols =~ m/\G\s*(.+?)(.*)\s*(?>,|\Z)/gcxo) {
			my ($select_expr) = $1;
			MKDEBUG && _d("Cannot parse expression \"$select_expr\"");
			my $col_struct = { expr => $select_expr, (), () };
			push @cols, $col_struct;
		}
		else {
			die "Column ident match on '$cols' failed";  # shouldn't happen
		}
	}

	return \@cols;
} # parse_columns # }}}

# Sub: parse_from # {{{
#   Parse a FROM clause, a.k.a. the table references.  Does not handle
#   nested joins.  See http://dev.mysql.com/doc/refman/5.1/en/join.html
#
# Parameters:
#   $from - FROM clause (with the word "FROM")
#
# Returns:
#   Arrayref of hashrefs, one hashref for each table in the order that
#   the tables appear, like:
#   (start code)
#   {
#     name           => 't2',  -- table's real name
#     alias          => 'b',   -- table's alias, if any
#     explicit_alias => 1,     -- if explicitly aliased with AS
#     join  => {               -- if joined to another table, all but first
#                              -- table are because comma implies INNER JOIN
#       to        => 't1',     -- table name on left side of join, if this is
#                              -- LEFT JOIN then this is the inner table, if
#                              -- RIGHT JOIN then this is outer table
#       type      => '',       -- left, right, inner, outer, cross, natural
#       condition => 'using',  -- on or using, if applicable
#       columns   => ['id'],   -- columns for USING condition, if applicable
#       ansi      => 1,        -- true of ANSI JOIN, i.e. true if not implicit
#                              -- INNER JOIN due to following a comma
#     },
#   },
#   {
#     name => 't3',
#     join => {
#       to        => 't2',
#       type      => 'left',
#       condition => 'on',     -- an ON condition is like a WHERE clause so
#       where     => [...]     -- this arrayref of predicates appears, see
#                              -- <parse_where()> for its structure
#     },
#   },
#  (end code)
sub parse_from( $$ ) {
	my ( $self, $from ) = @_;
	return unless $from;
	MKDEBUG && _d('Parsing FROM/INTO/TABLES', $from);

	# Extract the column list from USING(col, ...) clauses else
	# the inner commas will be captured by $comma_join.
	my $using_cols;
	($from, $using_cols) = $self->remove_using_columns($from);

	my $funcs;
	($from, $funcs) = $self->remove_functions($from);

	# Table references in a FROM clause are separated either by commas
	# (comma/theta join, implicit INNER join) or the JOIN keyword (ansi
	# join).  JOIN can be preceded by other keywords like LEFT, RIGHT,
	# OUTER, etc.  There must be spaces before and after JOIN and its
	# keywords, but there does not have to be spaces before or after a
	# comma.  See http://dev.mysql.com/doc/refman/5.5/en/join.html
	my $comma_join = qr/(?>\s*,\s*)/;
	my $ansi_join  = qr/(?>
	  \s+
	  (?:(?:INNER|CROSS|STRAIGHT_JOIN|LEFT|RIGHT|OUTER|NATURAL)\s+)*
	  JOIN
	  \s+
	)/xi;

	my @tbls;     # all table refs, a hashref for each
	my $tbl_ref;  # current table ref hashref
	my $join;     # join info hahsref for current table ref
	foreach my $thing ( split /($comma_join|$ansi_join)/io, $from ) {
		# We shouldn't parse empty things.
		die "Error parsing FROM clause" unless $thing;

		# Strip leading and trailing spaces.
		$thing =~ s/^\s+//;
		$thing =~ s/\s+$//;
		MKDEBUG && _d('Table thing:', $thing);

		if ( $thing =~ m/\s+(?:ON|USING)\s+/i ) {
			MKDEBUG && _d("JOIN condition");
			# This join condition follows a JOIN (comma joins don't have
			# conditions).  It includes a table ref, ON|USING, and then
			# the value to ON|USING.
			my ($tbl_ref_txt, $join_condition_verb, $join_condition_value)
				= $thing =~ m/^(.+?)\s+(ON|USING)\s+(.+)/i;

			$tbl_ref = $self->parse_table_reference($tbl_ref_txt);

			$join->{condition} = lc $join_condition_verb;
			if ( $join->{condition} eq 'on' ) {
				# The value for ON can be, as the MySQL manual says, is just
				# like a WHERE clause.
				$join->{where} = $self->parse_where($join_condition_value, $funcs);
			}
			else { # USING
				# Although calling parse_columns() works, it's overkill.
				# This is not a columns def as in "SELECT col1, col2", it's
				# a simple csv list of column names without aliases, etc.
				$join->{columns} = $self->_parse_csv(shift @$using_cols);
			}
		}
		elsif ( $thing =~ m/(?:,|JOIN)/i ) {
			# A comma or JOIN signals the end of the current table ref and
			# the begining of the next table ref.  Save the current table ref.
			if ( $join ) {
				$tbl_ref->{join} = $join;
			}
			push @tbls, $tbl_ref;
			MKDEBUG && _d("Complete table reference:", Dumper($tbl_ref));

			# Reset vars for the next table ref.
			$tbl_ref = undef;
			$join    = {};

			# Next table ref becomes the current table ref.  It's joined to
			# the previous table ref either implicitly (comma join) or explicitly
			# (ansi join).
			$join->{to} = $tbls[-1]->{tbl};
			if ( $thing eq ',' ) {
				$join->{type} = 'inner';
				$join->{ansi} = 0;
			}
			else { # ansi join
				my $type = $thing =~ m/^(.+?)\s+JOIN$/i ? lc $1 : 'inner';
				$join->{type} = $type;
				$join->{ansi} = 1;
			}
		}
		else {
			# First table ref and comma-joined tables.
			$tbl_ref = $self->parse_table_reference($thing);
			MKDEBUG && _d('Table reference:', Dumper($tbl_ref));
		}
	}

	# Save the last table ref.  It's not completed in the loop above because
	# there's no comma or JOIN after it.
	if ( $tbl_ref ) {
		if ( $join ) {
			$tbl_ref->{join} = $join;
		}
		push @tbls, $tbl_ref;
		MKDEBUG && _d("Complete table reference:", Dumper($tbl_ref));
	}

	return \@tbls;
} # parse_from
{
	no warnings;  # Why? See details below parse_insert
	*parse_into   = \&parse_from;
	*parse_tables = \&parse_from;
} # }}}

# Sub: parse_group_by # {{{
# GROUP BY {col_name | expr | position} [ASC | DESC], ... [WITH ROLLUP]
sub parse_group_by( $$ ) {
	my ( $self, $group_by ) = @_;
	return unless $group_by;
	MKDEBUG && _d('Parsing GROUP BY', $group_by);

	# Remove special "WITH ROLLUP" clause so we're left with a simple csv list.
	my $with_rollup = $group_by =~ s/\s+WITH ROLLUP\s*//i;

	# Parse the identifers.
	my $idents = $self->parse_identifiers( $self->_parse_csv($group_by) );

	$idents->{with_rollup} = 1 if $with_rollup;

	return $idents;
} # parse_group_by # }}}

sub parse_having( $$ ) { # {{{
	my ( $self, $having ) = @_;
	# TODO
	return $having;
} # parse_having # }}}

sub parse_identifier( $$$ ) { # {{{
	my ( $self, $type, $ident ) = @_;
	return unless defined $type && length $type && defined $ident && length $ident;
	MKDEBUG && _d("Parsing", $type, "identifier:", $ident);

	if ( $ident =~ m/^\w+\(/ ) {  # Function like MIN(col)
		my ($func, $expr) = $ident =~ m/^(\w+)\(([^\)]*)\)/;
		MKDEBUG && _d('Function', $func, 'arg', $expr);
		return { col => $ident } unless $expr;  # NOW()
		return { col => $expr } if( $expr =~ m/,/ ); # FIXME: Multiple arguments, which can't be trivially split as below...
		$ident = $expr;  # col from MAX(col)
	}

	my %ident_struct;
	my @ident_parts = map { s/`//g; $_; } split /[.]/, $ident;
	if ( @ident_parts == 3 ) {
		@ident_struct{qw(db tbl col)} = @ident_parts;
		#MKDEBUG && _d($type, "identifier 3 parts:", Dumper(\%ident_struct));
	}
	elsif ( @ident_parts == 2 ) {
		my @parts_for_type = $type eq 'column' ? qw(tbl col)
							    : $type eq 'table'  ? qw(db  tbl)
							    : die "Invalid identifier type: $type";
		@ident_struct{@parts_for_type} = @ident_parts;
		#MKDEBUG && _d($type, "identifier 2 parts:", Dumper(\%ident_struct));
	}
	elsif ( @ident_parts == 1 ) {
		my $part = $type eq 'column' ? 'col' : 'tbl';
		@ident_struct{($part)} = @ident_parts;
		#MKDEBUG && _d($type, "identifier 1 part:", Dumper(\%ident_struct));
	}
	else {
		die "Invalid number of parts '" . scalar( @ident_parts ) . "' in $type reference: $ident\n" . Dumper(\@ident_parts);
	}

	if ( $self->{Schema} ) {
		if ( $type eq 'column' && (!$ident_struct{tbl} || !$ident_struct{db}) ) {
			my $qcol = $self->{Schema}->find_column(%ident_struct);
			if ( $qcol && @$qcol == 1 ) {
				@ident_struct{qw(db tbl)} = @{$qcol->[0]}{qw(db tbl)};
			}
		}
		elsif ( !$ident_struct{db} ) {
			my $qtbl = $self->{Schema}->find_table(%ident_struct);
			if ( $qtbl && @$qtbl == 1 ) {
				$ident_struct{db} = $qtbl->[0];
			}
		}
	}

	MKDEBUG && _d($type, "return identifier struct:", Dumper(\%ident_struct));
	return \%ident_struct;
} # parse_identifier # }}}

# Sub: parse_identifiers # {{{
#   Parse an arrayref of identifiers into their parts.  Identifiers can be
#   column names (optionally qualified), expressions, or constants.
#   GROUP BY and ORDER BY specify a list of identifiers.
#
# Parameters:
#   $idents - Arrayref of indentifiers
#
# Returns:
#   Arrayref of hashes with each identifier's parts, depending on what kind
#   of identifier it is.
sub parse_identifiers( $$ ) {
	my ( $self, $idents ) = @_;
	return unless $idents;
	MKDEBUG && _d("Parsing identifiers");

	my @ident_parts;
	foreach my $ident ( @$idents ) {
		MKDEBUG && _d("Identifier:", $ident);
		my $parts = {};

		if ( $ident =~ s/\s+(ASC|DESC)\s*$//i ) {
			$parts->{sort} = uc $1;  # XXX
		}

		if ( $ident =~ m/^\d+$/ ) {      # Position like 5
			MKDEBUG && _d("Positional ident");
			$parts->{position} = $ident;
		}
		elsif ( $ident =~ m/^\w+\(/ ) {  # Function like MIN(col)
			MKDEBUG && _d("Expression ident");
			my ($func, $expr) = $ident =~ m/^(\w+)\(([^\)]*)\)/;
			$parts->{function}   = uc $func;
			$parts->{expression} = $expr if $expr;
		}
		else {                           # Ref like (table.)column
			MKDEBUG && _d("Table/column ident");
			my ($tbl, $col)  = $self->split_unquote($ident);
			$parts->{table}  = $tbl if $tbl;
			$parts->{column} = $col;
		}
		push @ident_parts, $parts;
	}

	return \@ident_parts;
} # parse_identifiers # }}}

# Sub: parse_limit # {{{
# [LIMIT {[offset,] row_count | row_count OFFSET offset}]
sub parse_limit( $$ ) {
	my ( $self, $limit ) = @_;
	return unless $limit;
	my $struct = {
		row_count => undef,
	};
	if ( $limit =~ m/(\S+)\s+OFFSET\s+(\S+)/i ) {
		$struct->{explicit_offset} = 1;
		$struct->{row_count}       = $1;
		$struct->{offset}          = $2;
	}
	else {
		my ($offset, $cnt) = $limit =~ m/(?:(\S+),\s+)?(\S+)/i;
		$struct->{row_count} = $cnt;
		$struct->{offset}    = $offset if defined $offset;
	}
	return $struct;
} # parse_limit # }}}

sub parse_modify( $$ ) { # {{{
	my ( $self, $modify ) = @_;
	# TODO
	return $modify;
} # parse_modify # }}}

# Sub: parse_order_by # {{{
# [ORDER BY {col_name | expr | position} [ASC | DESC], ...]
sub parse_order_by( $$ ) {
	my ( $self, $order_by ) = @_;
	return unless $order_by;
	MKDEBUG && _d('Parsing ORDER BY', $order_by);
	my $idents = $self->parse_identifiers( $self->_parse_csv($order_by) );
	return $idents;
} # parse_order_by # }}}

sub parse_set( $$ ) { # {{{
	my ( $self, $set ) = @_;
	MKDEBUG && _d("Parse SET", $set);
	return unless $set;
	my $vals = $self->_parse_csv($set);
	return unless $vals && @$vals;

	my @set;
	foreach my $col_val ( @$vals ) {
		# Do not remove quotes around the val because quotes let us determine
		# the value's type.  E.g. tbl might be a table, but "tbl" is a string,
		# and NOW() is the function, but 'NOW()' is a string.
		my ($col, $val)  = $col_val =~ m/^([^=]+)\s*=\s*(.+)/;
		my $ident_struct = $self->parse_identifier('column', $col);
		my $set_struct   = {
			%$ident_struct,
			value => $val,
		};
		MKDEBUG && _d("SET:", Dumper($set_struct));
		push @set, $set_struct;
	}
	return \@set;
} # parse_set # }}}

# Sub: parse_table_reference # {{{
# Parse a table ref like "tbl", "tbl alias" or "tbl AS alias", where
# tbl can be optionally "db." qualified.  Also handles FORCE|USE|IGNORE
# INDEX hints.  Does not handle "FOR JOIN" hint because "JOIN" here gets
# confused with the "JOIN" thing in parse_from().
sub parse_table_reference( $$ ) {
	my ( $self, $tbl_ref ) = @_;
	return unless $tbl_ref;
	MKDEBUG && _d('Parsing table reference:', $tbl_ref);
	my %tbl;

	# First, check for an index hint.  Remove and save it if present.
	# This can't be included in the $table_ident regex because, for example,
	# `tbl` FORCE INDEX (foo), makes FORCE look like an implicit alias.
	if ( $tbl_ref =~ s/
			\s+(
				(?:FORCE|USE|INGORE)\s
				(?:INDEX|KEY)
				\s*\([^\)]+\)\s*
			)//xi)
	{
		$tbl{index_hint} = $1;
		MKDEBUG && _d('Index hint:', $tbl{index_hint});
	}

	if ( $tbl_ref =~ m/$table_ident/ ) {
		my ($db_tbl, $as, $alias) = ($1, $2, $3); # XXX
		my $ident_struct = $self->parse_identifier('table', $db_tbl);
		$alias =~ s/`//g if $alias;
		@tbl{keys %$ident_struct} = values %$ident_struct;
		$tbl{explicit_alias} = 1 if $as;
		$tbl{alias}          = $alias if $alias;
	}
	else {
		die "Table ident match failed";  # shouldn't happen
	}

	return \%tbl;
} # parse_table_reference # }}}

# Sub: parse_vaules # {{{
# Parses the list of values after, e.g., INSERT tbl VALUES (...), (...).
# Does not currently parse each set of values; it just splits the list.
sub parse_values( $$ ) {
	my ( $self, $values ) = @_;
	return unless $values;

	my $vals;
	if( $values =~ m/^\s*\(.*\)\s*$/ ) {
		my @multivals;
		foreach my $match ( ( $values =~ m/$RE{ balanced }{ -begin => '(' }{ -end => ')' }/g ) ) {
			$match =~ s/^\s*\(\s*//;
			$match =~ s/\s*\)\s*$//;

			MKDEBUG && _d('parse_values: Multi-value item', $match );
			my $items = $self->_parse_csv(
				$match,
				quoted_values => 1,
				remove_quotes => 0,
			);
			#push( @multivals, @{ $items } );
			push( @multivals, $items );
		}
		$vals = \@multivals;
	} else {
		MKDEBUG && _d('parse_values: Simple list', $values );
		$vals = $self->_parse_csv(
			$values,
			quoted_values => 1,
			remove_quotes => 0,
		);
	}
	return $vals;
} # parse_values # }}}

# Sub: parse_where # {{{
# This is not your traditional parser, but it works for simple to rather
# complex cases, with a few noted and intentional limitations.  First,
# the limitations:
#
#   * probably doesn't handle every possible operator (see $op)
#   * doesn't care about grouping with parentheses
#   * not "fully" tested because the possibilities are infinite
#
# It works in four steps; let's take this WHERE clause as an example:
#
#   i="x and y" or j in ("and", "or") and x is not null or a between 1 and 10 and sz="this 'and' foo"
#
# The first step splits the string on and|or, the only two keywords I'm
# aware of that join the separate predicates.  This step doesn't care if
# and|or is really between two predicates or in a string or something else.
# The second step is done while the first step is being done: check predicate
# "fragments" (from step 1) for operators; save which ones have and don't
# have at least one operator.  So the result of step 1 and 2 is:
#
#   PREDICATE FRAGMENT                OPERATOR
#   ================================  ========
#   i="x                              Y
#   and y"                            N
#   or j in ("                        Y
#   and", "                           N
#   or")                              N
#   and x is not null                 Y
#   or a between 1                    Y
#   and 10                            N
#   and sz="this '                    Y
#   and' foo"                         N
#
# The third step runs through the list of pred frags backwards and joins
# the current frag to the preceding frag if it does not have an operator.
# The result is:
#
#   PREDICATE FRAGMENT                OPERATOR
#   ================================  ========
#   i="x and y"                       Y
#                                     N
#   or j in ("and", "or")             Y
#                                     N
#                                     N
#   and x is not null                 Y
#   or a between 1 and 10             Y
#                                     N
#   and sz="this 'and' foo"           Y
#                                     N
#
# The fourth step is similar but not shown: pred frags with unbalanced ' or "
# are joined to the preceding pred frag.  This fixes cases where a pred frag
# has multiple and|or in a string value; e.g. "foo and bar or dog".
#
# After the pred frags are complete, the parts of these predicates are parsed
# and returned in an arrayref of hashrefs like:
#
#   {
#     predicate => 'and',
#     column    => 'id',
#     operator  => '>=',
#     value     => '42',
#   }
#
# Invalid predicates, or valid ones that we can't parse,  will cause
# the sub to die.
sub parse_where( $$ ) {
	my ( $self, $where, $functions ) = @_;
	return unless $where;
	MKDEBUG && _d("Parsing WHERE", $where);

	# Not all the operators listed at
	# http://dev.mysql.com/doc/refman/5.1/en/non-typed-operators.html
	# are supported.  E.g. - (minus) is an op but does it ever show up
	# in a where clause?  "col-3=2" is valid (where col=5), but we're
	# not interested in weird stuff like that.
	my $op_symbol = qr/
		(?:
		 <=(?:>)?
		|^
		|~
		|<(?:<|>)?
		|=
		|>(?:>|=)?
		|-
		|:=
		|!(?:=)?
		|\|(?:\|)?
		|\/
		|\*
		|\+
		|&(?:&)?
		|%
		|AND
		|BINARY
		|CASE
		|DIV
		|MOD
		|NOT
		|OR
		|XOR
	)/xi;
	my $op_verb = qr/
		(?:
			 (?:(?:NOT\s+)?LIKE)
			|(?:IS(?:\s+NOT\s*)?)
			|(?:(?:NOT\s+)?BETWEEN)
			|(?:(?:NOT\s+)?IN)
			|(?:(?:NOT\s+)?EXISTS)
			|(?:(?:NOT\s+)?(?:REGEXP|RLIKE))
			|(?:SOUNDS\s+LIKE)
		)
	/xi;
	my $op_pat = qr/
	(
		(?>
			 (?:$op_symbol)  # don't need spaces around the symbols, e.g.: col=1
			|(?:\s+$op_verb) # must have space before verb op, e.g.: col LIKE ...
		)
	)/x;

	# Step 1 and 2: split on and|or and look for operators.
	my $offset = 0;
	my $pred   = "";
	my @pred;
	my @has_op;
	while ( $where =~ m/\b(and|or)\b/gi ) {
		my $pos = (pos $where) - (length $1);  # pos at and|or, not after

		$pred = substr $where, $offset, ($pos-$offset);
		push @pred, $pred;
		push @has_op, $pred =~ m/$op_pat/o ? 1 : 0;

		$offset = $pos;
	}
	# Final predicate fragment: last and|or to end of string.
	$pred = substr $where, $offset;
	push @pred, $pred;
	push @has_op, $pred =~ m/$op_pat/o ? 1 : 0;
	MKDEBUG && _d("Predicate fragments:", Dumper(\@pred));
	MKDEBUG && _d("Predicate frags with operators:", @has_op);

	# Step 3: join pred frags without ops to preceding pred frag.
	my $n = scalar @pred - 1;
	for my $i ( 1..$n ) {
		$i   *= -1;
		my $j = $i - 1;  # preceding pred frag

		# Two constants in a row, like "TRUE or FALSE", are a special case.
		# The current pred ($i) will not have an op but in this case it's
		# not a continuation of the preceding pred ($j) so we don't want to
		# join them.  And there's a special case within this special case:
		# "BETWEEN 1 AND 10".  _is_constant() strips leading AND or OR so
		# 10 is going to look like an independent constant but really it's
		# part of the BETWEEN op, so this whole special check is skipped
		# if the preceding pred contains BETWEEN.  Yes, parsing SQL is tricky.
		next if $pred[$j] !~ m/\s+between\s+/i  && $self->_is_constant($pred[$i]);

		if ( !$has_op[$i] ) {
			$pred[$j] .= $pred[$i];
			$pred[$i]  = undef;
		}
	}
	MKDEBUG && _d("Predicate fragments joined:", Dumper(\@pred));

	# Step 4: join pred frags with unbalanced ' or " to preceding pred frag.
	for my $i ( 0..@pred ) {
		$pred = $pred[$i];
		next unless defined $pred;
		my $n_single_quotes = ($pred =~ tr/'//);
		my $n_double_quotes = ($pred =~ tr/"//);
		if ( ($n_single_quotes % 2) || ($n_double_quotes % 2) ) {
			if( defined( $pred[$i + 1] ) ) {
				$pred[$i]     .= $pred[$i + 1];
				$pred[$i + 1]  = undef;
			} else {
				MKDEBUG && _d("Predicate fragments cannot be balanced on quotes:", Dumper(\@pred));
			}
		}
	}
	MKDEBUG && _d("Predicate fragments balanced:", Dumper(\@pred));

	# Parse, clean up and save the complete predicates.
	my @predicates;
	foreach my $pred ( @pred ) {
		next unless defined $pred;
		$pred =~ s/^\s+//;
		$pred =~ s/\s+$//;
		my $conj;
		if ( $pred =~ s/^(and|or)\s+//i ) {
			$conj = lc $1;
		}
		my ($col, $op, $val) = $pred =~ m/^(.+?)$op_pat(.+)$/o;
		if ( !$col || !$op ) {
			if ( $self->_is_constant($pred) ) {
				$val = lc $pred;
			}
			else {
				die "Failed to parse predicate \"$pred\" from WHERE condition \"$where\"";
			}
		}

		# Remove whitespace and lowercase some keywords.
		if ( $col ) {
			$col =~ s/\s+$//;
			$col =~ s/^\(+//;  # no unquoted column name begins with (
		}
		if ( $op ) {
			$op  =  lc $op;
			$op  =~ s/^\s+//;
			$op  =~ s/\s+$//;
		}
		$val =~ s/^\s+//;

		# No unquoted value ends with ) except FUNCTION(...)
		if ( ($op || '') !~ m/IN/i && $val !~ m/^\w+\([^\)]+\)$/ ) {
			$val =~ s/\)+$//;
		}

		if ( $val =~ m/NULL|TRUE|FALSE/i ) {
			$val = lc $val;
		}

		if ( $functions ) {
			$col = shift @$functions if $col =~ m/__FUNC\d+__/;
			$val = shift @$functions if $val =~ m/__FUNC\d+__/;
		}

		push @predicates, {
			predicate => $conj,
			left_arg  => $col,
			operator  => $op,
			right_arg => $val,
		};
	}

	return \@predicates;
} # parse_where # }}}

# Helper functions

# Sub: clean_query # {{{
#   Remove spaces, flatten, and normalize some patterns for easier parsing.
#
# Parameters:
#   $query - SQL statement
#
# Returns:
#   Cleaned $query
sub clean_query( $$ ) {
	my ( $self, $query ) = @_;
	return unless $query;

	# Whitespace and comments.
	$query =~ s/^\s*--.*$//gm;  # -- comments
	$query =~ s/\s+/ /g;        # extra spaces/flatten
	$query =~ s!/\*.*?\*/!!g;   # /* comments */
	$query =~ s/^\s+//;         # leading spaces
	$query =~ s/\s+$//;         # trailing spaces

	return $query;
} # clean_query # }}}

# Sub: is_identifier # {{{
#   Determine if something is a schema object identifier.
#   E.g.: `tbl` is an identifier, but "tbl" is a string and 1 is a number.
#   See <http://dev.mysql.com/doc/refman/5.1/en/identifiers.html>
#
# Parameters:
#   $thing - Name of something, including any quoting as it appears in a query.
#
# Returns:
#   True of $thing is an identifier, else false.
sub is_identifier( $$ ) {
	my ( $self, $thing ) = @_;

	# Nothing is not an ident.
	return 0 unless $thing;

	# Tables, columns, FUNCTIONS(), etc. cannot be 'quoted' or "quoted"
	# because that would make them strings, not idents.
	return 0 if $thing =~ m/\s*['"]/;

	# Numbers, ints or floats, are not identifiers.
	return 0 if $thing =~ m/^\s*\d+(?:\.\d+)?\s*$/;

	# Keywords are not identifiers.
	return 0 if $thing =~ m/^\s*(?>
		 NULL
		|DUAL
	)\s*$/xi;

	# The column ident really matches everything: db, db.tbl, db.tbl.col,
	# function(), @@var, etc.
	return 1 if $thing =~ m/^\s*$column_ident\s*$/;

	# If the thing isn't quoted and doesn't match our ident pattern, then
	# it's probably not an ident.
	return 0;
} # }}}

# Sub: normalize_keyword_spaces # {{{
#   Normalize spaces around certain SQL keywords.  Spaces are added and
#   removed around certain SQL keywords to make parsing easier.
#
# Parameters:
#   $query - SQL statement
#
# Returns:
#   Normalized $query
sub normalize_keyword_spaces( $$ ) {
	my ( $self, $query ) = @_;

	# Add spaces between important tokens to help the parse_* subs.
	$query =~ s/\b(VALUE(?:S)?)\(/$1 (/i;
	$query =~ s/\bON\(/on (/gi;
	$query =~ s/\bUSING\(/using (/gi;

	# Start of (SELECT subquery).
	$query =~ s/\(\s+SELECT\s+/(SELECT /gi;

	return $query;
} # normalize_keyword_spaces # }}}

sub remove_functions( $$ ) { # {{{
	my ($self, $clause) = @_;
	return unless $clause;
	MKDEBUG && _d('Removing functions from clause:', $clause);
	my @funcs;
	$clause =~ s/$function_ident/replace_function($1, \@funcs)/eg;
	MKDEBUG && _d('Function-stripped clause:', $clause, Dumper(\@funcs));
	return $clause, \@funcs;
} # }}}

# Sub: remove_subqueries # {{{
# Remove subqueries from query, return modified query and list of subqueries.
# Each subquery is replaced with the special token __SQn__ where n is the
# subquery's ID.  Subqueries are parsed and removed in to out, last to first;
# i.e. the last, inner-most subquery is ID 0 and the first, outermost
# subquery has the greatest ID.  Each subquery ID corresponds to its index in
# the list of returned subquery hashrefs after the modified query.  __SQ2__
# is subqueries[2].  Each hashref is like:
#   * query    Subquery text
#   * context  scalar, list or identifier
#   * nested   (optional) 1 if nested
# This sub does not handle UNION and it expects to that subqueries start
# with "(SELECT ".  See SQLParser.t for examples.
sub remove_subqueries( $$ ) {
	my ( $self, $query ) = @_;

	# FIXME: This function broadly does the correct thing (including
	#        the handling of SQL statements with multiple nested subqueries
	#        which aren't nested within each other) - but still appears to
	#        leave un-expanded __SQ{x}__ tokens in the resultant struct :(
	# FIXME: The last subquery seems to have the remainder of the query
	#        appended to it :(

	# Find starting pos of all subqueries.
	my @start_pos;
	while ( $query =~ m/(\(\s*SELECT\s+)/gi ) {
		my $pos = (pos $query) - (length $1);
		push @start_pos, $pos;
	}

	# Starting with the inner-most, last subquery, find ending pos of
	# all subqueries.  This is done by counting open and close parentheses
	# until all are closed.  The last closing ) should close the ( that
	# opened the subquery.  No sane regex can help us here for cases like:
	# (select max(id) from t where col in(1,2,3) and foo='(bar)').
	@start_pos = reverse @start_pos;
	my @end_pos;
	for my $i ( 0 .. $#start_pos ) {
		my $closed = 0;
		pos $query = $start_pos[$i];
		while ( $query =~ m/([\(\)])/cg ) {
			my $c = $1;
			$closed += ($c eq '(' ? 1 : -1);
			last unless $closed;
		}
		push @end_pos, pos $query;
	}

	# Replace each subquery with a __SQn__ token.
	my @subqueries;
	my $len_adj = 0;
	my $n    = 0;
	for my $i ( 0 .. $#start_pos ) {
		MKDEBUG && _d('Query:', $query);

		my $outerfound = 0;
		my $struct   = {};
		my $token    = '__SQ' . $n . '__';

MKDEBUG && _d("SQ: Using token '$token'");
		# Adjust len for next outer subquery.  This is required because the
		# subqueries' start/end pos are found relative to one another, so
		# when a subquery is replaced with its shorter __SQn__ token the end
		# pos for the other subqueries decreases.  The token is shorter than
		# any valid subquery so the end pos should only decrease.
		for my $j ( $i .. ( $#start_pos - 1 ) ) {
			next if( $outerfound );
MKDEBUG && _d("SQ: Iteration '$j' ($i to " . ( $#start_pos - 1 ) . ")");

			my $outer_start = $start_pos[$j + 1];
			my $outer_end   = $end_pos[$j + 1];
MKDEBUG && _d("SQ: Outer start $outer_start, Outer end $outer_end");

			if (    $outer_start && ($outer_start < $start_pos[$i])
				  && $outer_end   && ($outer_end   > $end_pos[$i]) ) {
				MKDEBUG && _d("Subquery $n nested within outer subquery " . ( $j + 1 ) );

				$len_adj = 0;
				for my $k ( 0 .. ( $i - 1 ) ) {
MKDEBUG && _d("SQ: Iteration '$k' (0 to " . ( $i - 1 ) . ")");
					my $inner_start = $start_pos[$k];
					my $inner_end   = $end_pos[$k];
MKDEBUG && _d("SQ: Inner start $inner_start, Inner end $inner_end");

					if (    $inner_start && ($inner_start > $start_pos[$i])
						  && $inner_end   && ($inner_end   < $end_pos[$i]) ) {
						my $inner_len = $inner_end - $inner_start;
						MKDEBUG && _d("Subquery $n contains nested subquery $k of length $inner_len");
						$len_adj += $inner_len - length $token;
					}
				}

				$struct->{nested} = $i + 1;
				$outerfound = 1;
			}
			MKDEBUG && _d("Nested subquery $n has total adjustment $len_adj");
		}
		if( not( $outerfound ) ) {
			MKDEBUG && _d("Subquery $n not nested");

			$len_adj = 0;
			#for my $k ( 0 .. ( $i - 1 ) ) {
			#	my $inner_start = $start_pos[$k];
			#	my $inner_end   = $end_pos[$k];
			#
			#	if (    $inner_start && ($inner_start > $start_pos[$i])
			#		  && $inner_end   && ($inner_end   < $end_pos[$i]) ) {
			#		my $inner_len = $inner_end - $inner_start;
			#		MKDEBUG && _d("Subquery $n contains nested subquery $k of length $inner_len");
			#		$len_adj += $inner_len - length $token;
			#	}
			#}
			#MKDEBUG && _d("Top-level subquery $n has total adjustment $len_adj");

			if ( $subqueries[-1] && $subqueries[-1]->{nested} ) {
				MKDEBUG && _d("Outermost subquery");
			}
		}
MKDEBUG && _d('SQ: start_pos:', Dumper(\@start_pos));
MKDEBUG && _d('SQ: end_pos:', Dumper(\@end_pos));
MKDEBUG && _d('SQ: subqueries:', Dumper(\@subqueries));

		my $len    = $end_pos[$i] - $start_pos[$i] - $len_adj;
		MKDEBUG && _d("Subquery $n start " . $start_pos[$i] .
				', orig end ' . $end_pos[$i] . ', adj ' .
				$len_adj . ', adj end ' . ( $start_pos[$i] + $len ) .
				', len ' . $len . '.' );
		my $subquery = substr($query, $start_pos[$i], $len, $token);
		MKDEBUG && _d("Subquery $n:", $subquery);

		# Get subquery context: scalar, list or identifier.
		if ( $query =~ m/(?:=|>|<|>=|<=|<>|!=|<=>)\s*$token/ ) {
			$struct->{context} = 'scalar';
		}
		elsif ( $query =~ m/\b(?:IN|ANY|SOME|ALL|EXISTS)\s*$token/i ) {
			# Add ( ) around __SQn__ for things like "IN(__SQn__)"
			# unless they're already there.
			if ( $query !~ m/\($token\)/ ) {
				$query =~ s/$token/\($token\)/;
				$len_adj -= 2 if $struct->{nested};
			}
			$struct->{context} = 'list';
		}
		else {
			# If the subquery is not preceded by an operator (=, >, etc.)
			# or IN(), EXISTS(), etc. then it should be an indentifier,
			# either a derived table or column.
			$struct->{context} = 'identifier';
		}
		MKDEBUG && _d("Subquery $n context:", $struct->{context});

		# Remove ( ) around subquery so it can be parsed by a parse_TYPE sub.
		$subquery =~ s/^\s*\(//;
		$subquery =~ s/\s*\)\s*$//;

		# Save subquery to struct after modifications above.
		$struct->{query} = $subquery;
		push @subqueries, $struct;
		$n++;
	}

	return $query, @subqueries;
} # }}}

sub remove_using_columns( $$ ) { # {{{
	my ($self, $from) = @_;
	return unless $from;
	MKDEBUG && _d('Removing cols from USING clauses');
	my $using = qr/
		\bUSING
		\s*
		\(
			([^\)]+)
		\)
	/xi;
	my @cols;
	$from =~ s/$using/push @cols, $1; "USING ($#cols)"/eg;
	MKDEBUG && _d('FROM:', $from, Dumper(\@cols));
	return $from, \@cols;
} # }}}

sub replace_function( $$ ) { # {{{
	my ($func, $funcs) = @_;
	my ($func_name) = $func =~ m/^(\w+)/;
	if ( !$ignore_function{uc $func_name} ) {
		my $n = scalar @$funcs;
		push @$funcs, $func;
		return "__FUNC${n}__";
	}
	return $func;
} # }}}

sub set_Schema( $$ ) { # {{{
	my ( $self, $sq ) = @_;
	$self->{Schema} = $sq;
	return;
} # }}}

# Sub: split_unquote # {{{
#   Split and unquote a table name.  The table name can be database-qualified
#   or not, like `db`.`table`.  The table name can be backtick-quoted or not.
#
# Parameters:
#   $db_tbl     - Table name
#   $default_db - Default database name to return if $db_tbl is not
#                 database-qualified
#
# Returns:
#   Array: unquoted database (possibly undef), unquoted table
sub split_unquote( $$$ ) {
	my ( $self, $db_tbl, $default_db ) = @_;
	$db_tbl =~ s/`//g;
	my ( $db, $tbl ) = split(/[.]/, $db_tbl);
	if ( !$tbl ) {
		$tbl = $db;
		$db  = $default_db;
	}
	return ($db, $tbl);
} # }}}

# Sub: _parse_clauses # {{{
#   Parse raw text of clauses into data structures.  This sub recurses
#   to parse the clauses of subqueries.  The clauses are read from
#   and their data structures saved into the $struct parameter.
#
# Parameters:
#   $struct - Hashref from which clauses are read (%{$struct->{clauses}})
#             and into which data structs are saved (e.g. $struct->{from}=...).
sub _parse_clauses( $$ ) {
	my ( $self, $struct ) = @_;
	# Parse raw text of clauses and functions.
	foreach my $clause ( keys %{$struct->{clauses}} ) {
		# Rename/remove clauses with space in their names, like ORDER BY.
		if ( $clause =~ m/\s+/ ) {
			(my $clause_no_space = $clause) =~ s/\s+/_/g;
			$struct->{clauses}->{$clause_no_space} = $struct->{clauses}->{$clause};
			delete $struct->{clauses}->{$clause};
			$clause = $clause_no_space;
		}

		# XXX: Hack to work around LIMIT gaining first argument bug
		$clause =~ s/_\d+$//;

		my $parse_func     = "parse_$clause";
		$struct->{$clause} = $self->$parse_func($struct->{clauses}->{$clause});

		if ( $clause eq 'select' ) {
			MKDEBUG && _d('Parsing subquery clauses');
			$struct->{select}->{type} = 'select';
			$self->_parse_clauses($struct->{select});
		}
	}
	return;
} # _parse_clauses # }}}

# Sub: _parse_csv # {{{
# Split any comma-separated list of values, removing leading
# and trailing spaces.
sub _parse_csv( $$$ ) {
	my ( $self, $vals, %args ) = @_;
	return unless $vals;

	MKDEBUG && _d("Parsing values:", $vals);

	my @vals;
	if ( $args{quoted_values} ) {
MKDEBUG && _d("Parsing values:", Dumper(\%args));
		# If the vals are quoted, then they can contain commas, like:
		# "hello, world!", 'batman'.  If only we could use Text::CSV,
		# then I wouldn't write yet another csv parser to handle this,
		# but Maatkit doesn't like package dependencies, so here's my
		# light implementation of this classic problem.
		my $quote_char   = '';
		VAL:
		foreach my $val ( split(',', $vals) ) {
			MKDEBUG && _d("Next value:", $val);
			# If there's a quote char, then this val is the rest of a previously
			# quoted and split value.
			if ( $quote_char ) {
				MKDEBUG && _d("Value is part of previous quoted value");
				# split() removed the comma inside the quoted value,
				# so add it back else "hello, world" is incorrectly
				# returned as "hello world".
				$vals[-1] .= ",$val";

				# Quoted and split value is complete when a val ends with the
				# same quote char that began the split value.
				if ( $val =~ m/[^\\]*$quote_char$/ ) {
					if ( $args{remove_quotes} ) {
						$vals[-1] =~ s/^\s*$quote_char//;
						$vals[-1] =~ s/$quote_char\s*$//;
					}
					MKDEBUG && _d("Previous quoted value is complete:", $vals[-1]);
					$quote_char = '';
				}

				next VAL;
			}

			# Start of new value so strip leading spaces but not trailing
			# spaces yet because if the next check determines that this is
			# a quoted and split val, then trailing space is actually space
			# inside the quoted val, so we want to preserve it.
			$val =~ s/^\s+//;

			# A value is quoted *and* split (because there's a comma in the
			# quoted value) if the vale begins with a quote char and does not
			# end with that char.  E.g.: "foo but not "foo".  The val "foo is
			# the first part of the split value, e.g. "foo, bar".
			if ( $val =~ m/^(['"])/ ) {
				MKDEBUG && _d("Value is quoted");
				$quote_char = $1;  # XXX
				if ( $val =~ m/.$quote_char$/ ) {
					MKDEBUG && _d("Value is complete");
					$quote_char = '';
					if ( $args{remove_quotes} ) {
						$vals[-1] =~ s/^\s*$quote_char//;
						$vals[-1] =~ s/$quote_char\s*$//;
					}
				}
				else {
					MKDEBUG && _d("Quoted value is not complete");
				}
			}
			else {
				$val =~ s/\s+$//;
			}

			# Save complete value (e.g. foo or "foo" without the quotes),
			# or save the first part of a quoted and split value; the rest
			# of such a value will be joined back above.
			MKDEBUG && _d("Saving value", ($quote_char ? "fragment" : ""));
			push @vals, $val;
		}
	}
	else {
		my $filteredline = $vals;
		my $strchanged = 0; # FALSE
		my $index = 0;
		my @savedterms;
		foreach my $match ( ( $vals =~ m/$RE{ balanced }{ -parens => '()' }/g ) ) {
			$filteredline =~ s/\Q$match\E/__MW_STR_${index}__/;
			MKDEBUG && _d("Replacing '$match' with '__MW_STR_${index}__' to give '$filteredline'");
			$index++;
			$savedterms[ $index ] = $match;
			$strchanged = 1; # TRUE
		}

		if( !( $strchanged ) ) {
			@vals = map { s/^\s+//; s/\s+$//; $_ } split(',', $vals);
		} else {
			MKDEBUG && _d("Quote-reduced line is now:", $filteredline) if( $strchanged );

			my @compressedvals = map { s/^\s+//; s/\s+$//; $_ } split(',', $filteredline);

			foreach my $val ( @compressedvals ) {
				while( $val =~ m/__MW_STR_(\d+)__/ ) {
					my $position = $1;
					if( $position >= $index ) {
						die( "Read placeholder string '$position' beyond maximum seen '$index'\n" );
					}
					my $replacement = $savedterms[ $position ];
					$replacement = '' unless( defined( $replacement ) and length( $replacement ) );
					$val =~ s/__MW_STR_${position}__/$replacement/;
					MKDEBUG && _d("Replacing '__MW_STR_${position}__' with '$replacement' to give '$val'");
				}
				push( @vals, $val );
			}
		}
	}
MKDEBUG && _d("Parsed values:", Dumper(\@vals));

	return \@vals;
}
{
	no warnings;  # Why? See same line above.
	*parse_on_duplicate = \&_parse_csv;
} # }}}

# Sub: _parse_query # {{{
#    This sub is called by the parse_TYPE subs except parse_insert.
#    It does two things: remove, save the given keywords, all of which
#    should appear at the beginning of the query; and, save (but not
#    remove) the given clauses.  The query should start with the values
#    for the first clause because the query's first word was removed
#    in parse().  So for "SELECT cols FROM ...", the query given here
#    is "cols FROM ..." where "cols" belongs to the first clause "columns".
#    Then the query is walked clause-by-clause, saving each.
#
# Parameters:
#   $query        - SQL statement with first word (SELECT, INSERT, etc.) removed
#   $keywords     - Compiled regex of keywords that can appear in $query
#   $first_clause - First clause word to expect in $query
#   $clauses      - Compiled regex of clause words that can appear in $query
#
# Returns:
#   Hashref with raw text of clauses
sub _parse_query( $$$$$ ) {
	my ( $self, $query, $keywords, $first_clause, $clauses ) = @_;
	return unless $query;
	my $struct = {};

	# Save, remove keywords.
	1 while $query =~ s/(?:^|\s+)(?:$RE{quoted}\s+)?$keywords(?:\s+$RE{quoted})?\s+/$struct->{keywords}->{lc $1}=1, ''/gie;

	# Go clausing.
	my @clause = grep { defined $_ }
		($query =~ m/\G(.+?)(?:(?:^|\s+)$clauses(?:\s+|$)|\Z)/gci);

	my $clause = $first_clause,
	my $value  = shift @clause;
	$struct->{clauses}->{$clause} = $value;
	MKDEBUG && _d('Clause:', $clause, $value);

	# All other clauses.
	while ( @clause ) {
		$clause = shift @clause;
		$value  = shift @clause;
		$struct->{clauses}->{lc $clause} = $value;
		MKDEBUG && _d('Clause:', $clause, $value);
	}

	($struct->{unknown}) = ($query =~ m/\G(.+)/);

	return $struct;
} # _parse_query # }}}

# Sub: _is_constant # {{{
# Returns true if the value is a constant.  Constants are TRUE, FALSE,
# and any signed number.  A leading AND or OR keyword is removed first.
sub _is_constant( $$ ) {
	my ( $self, $val ) = @_;
	return 0 unless defined $val;
	$val =~ s/^\s*(?:and|or)\s+//;
	return
		$val =~ m/^\s*(?:TRUE|FALSE)\s*$/i || $val =~ m/^\s*-?\d+\s*$/ ? 1 : 0;
} # }}}

sub _d { # {{{
	my ($package, undef, $line) = caller 0;
	@_ = map { (my $temp = $_) =~ s/\n/\n# /g; $temp; }
		  map { defined $_ ? $_ : 'undef' }
		  @_;
	print STDERR "# $package:$line $PID ", join(' ', @_), "\n";
} # _d # }}}

# ###########################################################################
# End SQLParser package
# ###########################################################################

# }}}
}

{
package myway;

use 5.014; # ... so that push/pop/etc work on scalars (experimental).

use strict;
use warnings;

no if ( $] >= 5.02 ), warnings => 'experimental::autoderef';
# ... because we should be able to push and splice via references, noting that
# this warning doesn't exist on earlier perl versions and so can't be
# unconditionally disabled.  Sigh.

# We have to enable and disable this module at run-time due to generating
# "Uncaught exception from user code" errors during certain DBI failures.
#use diagnostics;
# ... in actual fact, diagnostics causes more problems than it solves.  It does
# appear to be, in reality, quite silly.

use constant VERSION  =>  1.0.12;

use constant TRUE     =>  1;
use constant FALSE    =>  0;

use constant DEBUG    => ( $ENV{ 'DEBUG' } or FALSE );

use constant DEFDELIM => ';';

use constant PORT     =>  3306;
use constant MARKER   => '`<<VERSION>>';

# Necessary non-default modules:
#
# * DBI::Format ( DBI::Shell, Text::Reform, IO::Tee )
# * File::Touch ()
# * File::Which ()
# * match::smart ()
# * Regexp::Common ()
# * Sort::Versions ()
#

use v5.10;
use match::smart;

use Cwd qw( getcwd realpath );
use DBI;
use DBI::Format;
use File::Basename;
use File::Copy;
use File::Glob qw( :glob );
use File::Path qw( make_path );
use File::Temp;
use File::Touch;
use File::Which;
use FileHandle;
use Getopt::Long qw( GetOptionsFromArray );
use Pod::Usage;
use Regexp::Common;
use Sort::Versions;
use Time::HiRes qw( gettimeofday tv_interval );

use Data::Dumper;

# Modules not currently used in latest code:
#use Clone qw( clone );
#use Data::ShowTable;
#use Filter::Indent::HereDoc;
#use JSON;
#use Net::Netmask;
#use Net::Subnet;
#use Sort::Key::Multi qw( i3_keysort );
#use SQL::Parser;
#use SQL::Tokenizer qw( tokenize_sql );
#use Sys::Hostname;

sub pdebug( $;$ );
sub pnote( $;$ );
sub pwarn( $;$ );
sub pfatal( $;$ );
sub getvalue( $$ );
sub initstate();
sub compressquotes( $$ );
sub decompressquotes( $$ );
sub checkentry( $$;$$ );
sub pushstate( $$ );
sub pushentry( $$$$$;$ );
sub pushfragment( $$$;$$ );
sub processcomments( $$$;$ );
sub processline( $$;$$ );
sub processfile( $$;$$$ );
sub dbopen( $$$$;$$ );
sub dbclose( ;$$ );
sub dbdump( $;$$$$$ );
sub dbrestore( $$ );
sub dosql( $$ );
sub preparesql( $$ );
sub executesql( $$$;@ );
sub getsqlvalue( $$ );
sub getsqlvalues( $$;$ );
sub outputtable( $$;$ );
sub formatastable( $$$ );
sub applyschema( $$$$;$ );
sub main( @ );

our $fatal   = "FATAL:";
our $warning = "WARN: ";

our $verbosity = 0;


our $flywaytablename = 'schema_version';
our $flywayddl  = <<DDL;
CREATE TABLE IF NOT EXISTS `$flywaytablename` (
    `version_rank`	INT		                          NOT NULL
  , `installed_rank`	INT		                          NOT NULL
  , `version`		VARCHAR(50)	                          NOT NULL
  , `description`	VARCHAR(200)	                          NOT NULL
  , `type`		VARCHAR(20)	                          NOT NULL
  , `script`		VARCHAR(1000)	                          NOT NULL
  , `checksum`		INT		DEFAULT NULL
  , `installed_by`	VARCHAR(100)	                          NOT NULL
  , `installed_on`	TIMESTAMP	DEFAULT CURRENT_TIMESTAMP NOT NULL
  , `execution_time`	INT		                          NOT NULL
  , `success`		BOOLEAN		                          NOT NULL
  , PRIMARY KEY                         (`version`)
  ,         KEY `schema_version_vr_idx` (`version_rank`)
  ,         KEY `schema_version_ir_idx` (`installed_rank`)
  ,         KEY `schema_version_s_idx`  (`success`)
) ENGINE='InnoDB' DEFAULT CHARSET='UTF8';
DDL

# Note that field-lengths in myway* tables are not arbitrary, but instead are
# sized to hold the maximum permissible value for the field-type, according to
# the appropraite standards - mostly POSIX.
#
# TIMESTAMP fields must be provided with a non-zero default value (or NULL)
# as the //second// and further TIMESTAMP fields will be implicitly created
# as DEFAULT 0, which breaks when NO_ZERO_DATE is in effect...
#
our $mywaytablename = 'myway_schema_version';
our $mywayddl  = <<DDL;
CREATE TABLE IF NOT EXISTS `$mywaytablename` (
    `id`		CHAR(36)	                          NOT NULL
  , `dbuser`		CHAR(16)	                          NOT NULL
  , `dbhost`		CHAR(64)	                          NOT NULL
  , `osuser`		CHAR(32)	                          NOT NULL
  , `host`		CHAR(64)	                          NOT NULL
  , `sha1sum`		CHAR(40)	                          NOT NULL
  , `path`		VARCHAR(4096)	CHARACTER SET 'UTF8'      NOT NULL
  , `filename`		VARCHAR(255)	CHARACTER SET 'UTF8'      NOT NULL
  , `started`		TIMESTAMP
  , `sqlstarted`	TIMESTAMP	DEFAULT NULL                  NULL
  , `finished`		TIMESTAMP	DEFAULT NULL                  NULL
  , `status`		TINYINT		UNSIGNED
  , PRIMARY KEY (`id`)
) ENGINE='InnoDB' DEFAULT CHARSET='ASCII';
DDL

# Previously, `statement` was of type VARCHAR(16384) - but SQL statements may
# be as many bytes as specified by the 'max_allowed_packet' variable, which
# defaults to 16MB.  To cope with this without truncation, we must use a TEXT
# field-type.  It is possible that, since this occurance is rare, it would be
# more advantageous performance-wise to store two fields: one for 'short' lines
# (of up to 32676 UTF-8 characters) and one for lines that wouldn't fit into a
# maximally-sized VARCHAR()...
#
our $mywayactionsname = 'myway_schema_actions';
our $mywayactionsddl  = <<DDL;
CREATE TABLE IF NOT EXISTS `$mywayactionsname` (
    `schema_id`		CHAR(36)	                          NOT NULL
  , `started`		TIMESTAMP(6)	DEFAULT CURRENT_TIMESTAMP NOT NULL
  , `event`		VARCHAR(256)	                          NOT NULL
  , `statement`		LONGTEXT	CHARACTER SET 'UTF8'      NOT NULL
  , `line`		BIGINT		UNSIGNED
  , `time`		DECIMAL(13,3)
  , `state`		CHAR(5)
  , INDEX        `${mywayactionsname}_schema_id_idx` (`schema_id`)
  , CONSTRAINT   `${mywayactionsname}_schema_id_${mywaytablename}_id`
    FOREIGN KEY (`schema_id`) REFERENCES `$mywaytablename` (`id`)
    ON DELETE CASCADE
) ENGINE='InnoDB' DEFAULT CHARSET='ASCII';
DDL

our $mywayprocsname = 'myway_stored_procedures';
our $mywayprocsddl  = <<DDL;
CREATE TABLE IF NOT EXISTS `$mywayprocsname` (
    `id`		CHAR(36)	                          NOT NULL
  , `dbuser`		CHAR(16)	                          NOT NULL
  , `dbhost`		CHAR(64)	                          NOT NULL
  , `osuser`		CHAR(32)	                          NOT NULL
  , `host`		CHAR(64)	                          NOT NULL
  , `sha1sum`		CHAR(40)	                          NOT NULL
  , `path`		VARCHAR(4096)	CHARACTER SET 'UTF8'      NOT NULL
  , `filename`		VARCHAR(255)	CHARACTER SET 'UTF8'      NOT NULL
  , `version`		VARCHAR(50)	CHARACTER SET 'UTF8'
  , `description`	VARCHAR(200)	CHARACTER SET 'UTF8'
  , `type`		VARCHAR(20)	CHARACTER SET 'UTF8'
  , `started`		TIMESTAMP
  , `sqlstarted`	TIMESTAMP	DEFAULT NULL                  NULL
  , `finished`		TIMESTAMP	DEFAULT NULL                  NULL
  , `status`		TINYINT		UNSIGNED
  , PRIMARY KEY (`id`)
) ENGINE='InnoDB' DEFAULT CHARSET='ASCII';
DDL

sub pdebug( $;$ ) { # {{{
	my( $text, $verbose ) = @_;
	$verbose = $verbosity unless( defined( $verbose ) );

	our $debug = "DEBUG: ";

	warn( "$debug $text\n" ) if( DEBUG or ( $verbose > 2 ) );

	return( DEBUG or ( $verbose > 2 ) );
} # pdebug # }}}

sub pnote( $;$ ) { # {{{
	my( $text, $verbose ) = @_;
	$verbose = $verbosity unless( defined( $verbose ) );

	our $note = "NOTICE:";

	warn( "$note $text\n" ) if( $verbose > 1 );

	return( $verbose > 1 );
} # pnote # }}}

sub pwarn( $;$ ) { # {{{
	my( $text, $verbose ) = @_;
	$verbose = $verbosity unless( defined( $verbose ) );

	warn( "$warning $text\n" ) if( $verbose > 0 );

	return( $verbose > 0 );
} # pwarn # }}}

sub pfatal( $;$ ) { # {{{
	my( $text, $ignored ) = @_;

	warn( "$fatal $text\n" );

	return( TRUE );
} # pfatal # }}}

sub initstate() { # {{{

	# Known single-line comments
	my @slc = (
		  '#'
		,  qw( // -- )
	);
	# Known multi-line comment pairs
	my %mlc = (
		  '\/\*'	=> '\*\/'
		, '\{'		=> '\}'
	);
	## Known quotation symbols
	#my @quo = (
	#	  '`'
	#	, "'"
	#	, '"'
	#);
	my @str = ();

	my %state = (
		  'file'	=>	 undef	# Current filename, for logging purposes
		, 'symbol'	=>       undef	# Used to hold the closing characters of a multi-line comment or statement delimiter
		, 'depth'	=>       0	# Comment nesting depth
		, 'line'	=>	 0	# Line of input on which current entry starts
		, 'type'	=>	 undef	# Entry type: comment, statement, or fragment
		, 'entry'	=>	 undef	# Current entry contents
	);

	@{ $state{ 'slc' } } = @slc;
	%{ $state{ 'mlc' } } = %mlc;
	#@{ $state{ 'quo' } } = @quo;
	@{ $state{ 'str' } } = @str;

	return( \%state );
} # initstate # }}}

sub compressquotes( $$ ) { # {{{
	my( $line, $state ) = @_;

	#my @quo = @{ $state -> { 'quo' } };
	#my $quochanged = FALSE;

	## Try to isolate any quoted text (to be expanded out later) so that we
	## aren't trying to comment-check user-data...
	##
	#for( my $index = 0 ; $index < scalar( @quo ) ; $index++ ) {
	#	my $character = $quo[ $index ];
	#	$quochanged = TRUE if( $line =~ s/(\\$character|$character$character)/__MW_QUO_${index}__/g );
	#}
	#pdebug( "  q Escaped-quote filtered line is now '$line'" ) if( $quochanged );

	# We're only going to attempt to handle quoted text which starts and
	# ends on the same line.  However, a string such as:
	#
	#     don't do this */ /* don't do this either
	#
	# ... is problematic because the central portion does appear to be a
	# valid quoted string.  If we were to process comments first and only
	# look for quoted strings outside of comments, then we risk thinking
	# that text within a quoted string such as:
	#
	#     mime-type: text/*
	#
	# ... is actually the start of a comment.  At least we can ensure that
	# apparent quotes are balanced before we consider them...
	#
	my $filteredline = $line;
	my $strchanged = FALSE;
	foreach my $match ( ( $line =~ m/$RE{ quoted }/g ) ) {
		my $index = scalar( @{ $state -> { 'str' } } );
		$filteredline =~ s/\Q$match\E/__MW_STR_${index}__/;
		push( $state -> { 'str' }, $match );
		$strchanged = TRUE;
		pdebug( "  q Replacing '$match' with '__MW_STR_${index}__' to give '$filteredline'" );
	}
	#pdebug( "  q Quote-reduced line is now '$filteredline'" ) if( $quochanged or $strchanged );
	pdebug( "  q Quote-reduced line is now '$filteredline'" ) if( $strchanged );

	return( $filteredline );
} # compressquotes # }}}

sub decompressquotes( $$ ) { # {{{
	my( $line, $state ) = @_;

	return( undef ) unless( defined( $line ) and length( $line ) );

	# This function must perform the exact opposite of compressquotes(),
	# above...

	my @str = @{ $state -> { 'str' } };
	my $strchanged = FALSE;

	if( scalar( @str ) ) {
		# For some reason, I can't initialise with scalar( @str ) and
		# then decrement with --$index?
		#
		for( my $index = ( scalar( @str ) - 1 ) ; $index >= 0 ; $index-- ) {
			my $match = $str[ $index ];
			if( defined( $match ) and length( $match ) ) {
				if( $line =~ s/__MW_STR_${index}__/$match/ ) {
					pdebug( "  Q Replaced '__MW_STR_${index}__' wth '$match' to give '$line'" );
					$strchanged = TRUE;
					@{ $state -> { 'str' } }[ $index ] = undef;
				}
			}
		}
	}

	#my @quo = @{ $state -> { 'quo' } };
	my $quochanged = FALSE;

	#if( scalar( @quo ) ) {
	#	for( my $index = ( scalar( @quo ) - 1 ) ; $index >= 0 ; $index -- ) {
	#		my $character = $quo[ $index ];

	#		# We don't store whether the character was backslash-
	#		# escaped or double-character escaped - let's default
	#		# to the former, on the basis of it being more
	#		# obivous...
	#		#
	#		if( $line =~ s/__MW_QUO_${index}__/\\$character/g ) {
	#			$quochanged = TRUE;
	#		}
	#	}
	#	pdebug( "  Q Escaped-quote filtered line is now '$line'" ) if( $quochanged );
	#}

	pdebug( "  Q Quote-expanded line is now '$line'" ) if( $quochanged or $strchanged );

	return( $line );
} # decompressquotes # }}}

sub checkentry( $$;$$ ) { # {{{
	my ( $data, $state, $description, $line ) = @_;

	$line = $. unless( defined( $line ) );

	if( defined( $state -> { 'entry' } ) and scalar( @{ $state -> { 'entry' } } ) ) {
		pdebug( "  * " . ( defined( $description ) ? $description . ' n' : 'N' ) . "esting error near line $line - " . scalar( @{ $state -> { 'entry' } } ) . " fragment(s) still defined - adding regardless" );
		my $count = 0;
		foreach my $entry ( @{ $state -> { 'entry' } } ) {
			$count++;
			pdebug( "--- \$state $count contains '$entry'" );
		}

		$state -> { 'entry' } = 'fragment';
		if( defined( $data -> { 'entries' } ) ) {
			push( $data -> { 'entries' }, { 'line' => $state -> { 'line' }, 'type' => $state -> { 'type' }, 'entry' => $state -> { 'entry' } } );
		} else {
			$data -> { 'entries' } = [ { 'line' => $state -> { 'line' }, 'type' => $state -> { 'type' }, 'entry' => $state -> { 'entry' } } ];
		}
		$state -> { 'line' } = 0;
		undef( $state -> { 'type' } );
		undef( $state -> { 'entry' } );

		$count = scalar( @{ $data -> { 'entries' } } );
		pdebug( "... we now have $count " . ( ( 1 == $count ) ? 'entry' : 'entries' ) );

		return( FALSE );
	}

	return( TRUE );
} # checkentry # }}}

sub pushentry( $$$$$;$ ) { # {{{
	my( $data, $state, $type, $entry, $description, $line ) = @_;

	$line = $. unless( defined( $line ) );

	pdebug( "  E Adding " . ( defined( $description ) ? $description . ' ' : '' ) . "entry '$entry' of type '$type' from line $line ..." );

	checkentry( $data, $state, $description, $line );

	my $element;
	$element -> { 'line' } = $line;
	$element -> { 'type' } = $type;
	$element -> { 'entry' } = $entry;

	pdebug( "  E Pushing $type '$entry' ..." );
	if( defined( $data -> { 'entries' } ) ) {
		push( $data -> { 'entries' }, $element );
	} else {
		$data -> { 'entries' } = [ $element ];
	}

	my $count = scalar( @{ $data -> { 'entries' } } );
	pdebug( "... we now have $count " . ( ( 1 == $count ) ? 'entry' : 'entries' ) );

	return( $count );
} # pushentry # }}}

sub pushstate( $$ ) { # {{{
	my( $data, $state ) = @_;

	my $entries = "entries";
	my $count = 0;
	$count = scalar( @{ $state -> { 'entry' } } ) if( defined( $state -> { 'entry' } ) );
	$entries = "entry" if( 1 == $count );

	my $element;
	$element -> { 'line' } = $state -> { 'line' } if( defined( $state -> { 'line' } ) );
	$element -> { 'type' } = $state -> { 'type' } if( defined( $state -> { 'type' } ) );
	$element -> { 'entry' } = $state -> { 'entry' } if( defined( $state -> { 'entry' } ) );
	$element -> { 'tokens' } = $state -> { 'tokens' } if( defined( $state -> { 'tokens' } ) );

	if( defined( $data -> { 'entries' } ) ) {
		pdebug( "  T Adding $count $entries from \$state to \$data -> { 'entries' } ..." );

		push( $data -> { 'entries' }, $element );
	} else {
		pdebug( "  T Setting \$data -> { 'entries' } to $count $entries from \$state" );

		$data -> { 'entries' } = [ $element ];
	}

	$count = scalar( @{ $data -> { 'entries' } } );
	pdebug( "  T ... we now have $count " . ( ( 1 == $count ) ? 'entry' : 'entries' ) );

	return( $count );
} # pushstate # }}}

sub pushfragment( $$$;$$ ) { # {{{
	my( $state, $type, $entry, $description, $line ) = @_;

	$line = $. unless( defined( $line ) );

	pdebug( "  F Adding " . ( defined( $description ) ? $description . ' ' : '' ) . "fragment '$entry' of type '$type' from line $line ..." );

	if( defined( $state -> { 'entry' } ) ) {
		push( $state -> { 'entry' }, ( defined( $entry ) ? $entry : '' ) );
	} else {
		$state -> { 'line' } = $line;
		$state -> { 'type' } = $type;
		$state -> { 'entry' } = [ ( defined( $entry ) ? $entry : '' ) ];
	}

	my $count = scalar( @{ $state -> { 'entry' } } );
	pdebug( "  F ... current fragment contains $count " . ( ( 1 == $count ) ? 'line' : 'lines' ) );
	#pdebug( "  F ... current fragment contains $count " . ( ( 1 == $count ) ? 'line' : 'lines' ) . ':' );
	#for( my $n = 0 ; $n < $count ; $n++ ) {
	#	pdebug( '  F ... ' . ( $n + 1 ) . ': ' . @{ $state -> { 'entry' } }[ $n ] );
	#}
	#pdebug( '  F ... EOF' );

	return( $count );
} # pushfragment # }}}

sub processcomments( $$$;$ ) { # {{{
	my( $data, $line, $masterstate, $strict ) = @_;

	return( undef ) unless( defined( $masterstate -> { 'comments' } ) );

	my $state = $masterstate -> { 'comments' };

	my @slc = @{ $state -> { 'slc' } };
	my %mlc = %{ $state -> { 'mlc' } };

	$line = compressquotes( $line, $masterstate );

	# Handle comments

	if( 0 == $state -> { 'depth' } ) {
		pdebug( "  C  Comment depth == 0" );

		# Check for comments which are capable of extending over
		# multiple lines, but which start and end on this line alone.
		#
		foreach my $start ( keys( %mlc ) ) {
			my $end = $mlc{ $start };

			$start =~ s/\\//g;
			$end =~ s/\\//g;
			pdebug( "  C Checking for balanced multi-line comment between '$start' and '$end' ..." );

			foreach my $match ( ( $line =~ m/$RE{ balanced }{ -begin => $start }{ -end => $end }{ -keep }/g ) ) {
				pdebug( "  C ... matched on sub-string '$match'" );

				pushentry( $data, $state, 'comment', decompressquotes( $match, $masterstate ), "Single-line" );

				# Ensure that Hints don't leave a trailing
				# semi-colon (but also ensure that Hint-like
				# comments do always have the correct
				# terminator)...
				#$match .= DEFDELIM if( $match =~ m:^/\*![0-9]{5} (.+) \*/$: );
				# This should no longer happen, as hints don't
				# get passed to this code-path.

				$line =~ m/^(.*?)\Q$match\E(.*?)$/;
				my $pre = $1;
				my $post = $2;
				$line = ( defined( $pre ) ? $pre : '' ) . ( defined( $post ) ? $post : '' );
				pdebug( "  C * \$line is now '$line' ('$match' removed)" );
			}
			pdebug( "  C Matches complete - post-match \$line is '$line'" );
			pdebug( "  C Empty line - returning" ) unless( length( $line ) );
			return( undef ) unless( length( $line ) );
		}
		pdebug( "  C Filtered text is '$line'" );

		# Comments which open and close on the same line have now been
		# removed - so now check for the start of actual multi-line
		# comments...
		#
		MLC: foreach my $start ( keys( %mlc ) ) {
			my $regex = $start . '.*$';

			eval { qr/$regex/ };
			die( "$fatal Invalid regex '$regex'" . ( ( defined( $state -> { 'file' } ) and length( $state -> { 'file' } ) ) ? " in file '" . $state -> { 'file' } . "'" : '' ) . ": $@\n" ) if( $@ );

			pdebug( "  C Checking for multi-line initial token '$regex' ..." );

			if( $line =~ m/$regex/ ) {
				pdebug( "  C Match on '$regex'" );

				$state -> { 'symbol' } = $mlc{ $start };
				my( $pre, $post ) = split( /$start/, $line );
				pdebug( "  C Sections are '$pre' & '$post'" );

				( my $filtered = $pre ) =~ s/\s+//g;
				if( defined( $filtered ) and length( $filtered ) ) {
					pdebug( "  C Processing text before comment '$pre' ..." );
					$line = processline( $data, $pre, $masterstate, $strict );
				} else {
					pdebug( "  C Empty line, save for comment" );
					undef( $line );
				}

				$start =~ s/\\//g;
				pdebug( "  C Adding starting fragment '$start$post'" );

				checkentry( $data, $state, 'Multi-line' );

				$state -> { 'line' } = $.;
				$state -> { 'type' } = 'comment';
				$state -> { 'entry' } = [ $start . $post ];
				pdebug( "  C ... current comment contains " . scalar( @{ $state -> { 'entry' } } ) . " lines ..." );

				$state -> { 'depth' } ++;

				( $filtered = $line ) =~ s/\s+//g if( defined( $line ) );
				if( defined( $filtered ) and length( $filtered ) ) {
					pdebug( "  C Remaining text is '$line', depth " . $state -> { 'depth' } );
				} else {
					pdebug( "  C No remaining text, depth " . $state -> { 'depth' } );
					last MLC
				}
			}
		}

		SLC: foreach my $token ( @slc ) {
			my $regex = quotemeta( $token ) . '.*$';

			pdebug( "  C Checking for single-line token '$regex' ..." );
			if( length( $line ) and ( $line =~ m/$regex/ ) ) {
				( my $comment = $line ) =~ s/^.*?\Q$token\E/$token/;
				$line =~ s/$regex//g;

				checkentry( $data, $state, 'One-line' );

				if( defined( $comment ) ) {
					pdebug( "  C Found single-line comment '$comment', remaining text '$line'" );

					pushentry( $data, $state, 'comment', decompressquotes( $comment, $masterstate ), 'One-line' );
				}

				pdebug( "  C Processing line before comment '$line' ..." ) if( length( $line ) );

				#$line = processline( $data, $line, $masterstate, $strict ) if( length( $line ) );
				( my $filtered = $line ) =~ s/\s+//g;
				if( defined( $filtered ) and length( $filtered ) ) {
					return( processline( $data, $line, $masterstate, $strict ) );
				} else {
					return( undef );
				}
			}

			#pdebug( "  C Empty line - returning" ) unless( length( $line ) );
			#return( undef ) unless( length( $line ) );
		}


	} else { # ( 0 != $state -> { 'depth' } )
		die( "$fatal Logic error" . ( ( defined( $state -> { 'file' } ) and length( $state -> { 'file' } ) ) ? " in file '" . $state -> { 'file' } . "'" : '' ) ) unless( defined( $state -> { 'symbol' } ) );

		pdebug( "  C In a comment, depth " . $state -> { 'depth' } . " ..." );

		# Remove embedded multi-line comments on one
		# line...
		my $end = $state -> { 'symbol' };
		my %values = reverse( %mlc );
		my $start = $values{ $end };
		undef( %values );

		( my $ustart = $start ) =~ s/\\//g;
		( my $uend = $end ) =~ s/\\//g;

		unless( ( 1 == $state -> { 'depth' } ) and ( $line =~ m/$end/ ) ) {
			pushfragment( $state, 'comment', decompressquotes( $line, $masterstate ), 'mid-comment' );

			return( undef );
		}

		pdebug( "  C Checking '$line' for balanced multi-line comment between '$ustart' and '$uend' (depth " . $state -> { 'depth' } . ") ..." );
		foreach my $match ( ( $line =~ m/$RE{ balanced }{ -begin => $ustart }{ -end => $uend }{ -keep }/g ) ) {
			pdebug( "  C Matched sub-string '$match'" );

			#$match =~ s/\*/\\*/g;
			#$match =~ s/\//\\\//g;
			#$match =~ s/\(/\\(/g;
			#$match =~ s/\)/\\)/g;
			##$line =~ s/($match)//;
			##my( $pre, $post ) = split( /$match/, $line );
			$line =~ m/^(.*?)\Q$match\E(.*?)$/;
			my $pre = $1;
			my $post = $2;
			$line = ( defined( $pre ) ? $pre : '' ) . ( defined( $post ) ? $post : '' );
			pdebug( "  C \$line is now '$line' ('$match' removed)" );
		}
		pdebug( "  C Post-match \$line is '$line'" );

		return( undef ) unless( length( $line ) );

		# We're currently inside a multi-line comment,
		# which either contains one or more significant opening
		# comments or one or more significant closing comments...
		#
		if( $line =~ m/$start/ ) {
			pdebug( "  C Match on start '$start'" );

			# A nested comment starts here
			#
			my( $pre, $post ) = split( /$start/, $line );
			pdebug( "  C Sections are '$pre' & '$post'" );
			if( length( $pre ) ) {
				pdebug( "  C Processing text before nested comment '$pre' ..." );

				$line = processline( $data, $pre, $masterstate, $strict );
			} else {
				pdebug( "  C Empty line" );

				undef( $line );
			}
			pdebug( "  C Processing text after nested comment '$post' ..." ) if( length( $post ) );

			processline( $data, $post, $masterstate, $strict ) if( length( $post ) );

			$state -> { 'depth' } ++;

			pdebug( "  C Remaining text is '$line', depth " . $state -> { 'depth' } ) if( defined( $line ) );

		} elsif( $line =~ m/$end/ ) {
			pdebug( "  C Match on end '$end'" );

			# Comment ends on this line
			if( not( ( $state -> { 'depth' } ) > 0 ) ) {
				pdebug( "  C Depth nesting error on line $." );
				$state -> { 'depth' } = 1;
			}
			$state -> { 'depth' } --;

			my( $pre, $post ) = split( /$end/, $line );

			pdebug( "  C Sections are '$pre' & '$post' (depth " . $state -> { 'depth' } . ")" );

			# $depth is already decremented above...
			#
			if( 0 == $state -> { 'depth' } ) {
				$end =~ s/\\//g;

				pushfragment( $state, 'comment', decompressquotes( ( defined( $pre ) ? $pre : '' ) . $end, $masterstate ), 'ending' );

				pdebug( "  C Pushing resultant comments array ..." );
				pushstate( $data, $state );
				$state -> { 'line' } = 0;
				undef( $state -> { 'type' } );
				undef( $state -> { 'entry' } );
			}

			if( length( $post ) ) {
				pdebug( "  C Processing text after comment '$post' ..." );
				$line = processline( $data, $post, $masterstate, $strict );
			} else {
				pdebug( "  C Empty line" );
				undef( $line );
			}

			( my $filtered = $line ) =~ s/\s+//g if( defined( $line ) );
			if( defined( $filtered ) and length( $filtered ) ) {
				pdebug( "  C Remaining text is '$line', depth " . $state -> { 'depth' } );
			} else {
				pdebug( "  C No remaining text, depth " . $state -> { 'depth' } );
			}

		} else {
			pdebug( "  C Empty line - returning" );

			return( undef );
		}
	} # $state -> { 'depth' }

	pdebug( "  C End processing text for comments." );

	return( decompressquotes( $line, $masterstate ) );
} # processcomments # }}}

sub processline( $$;$$ ) { # {{{
	my( $data, $line, $state, $strict ) = @_;

	if( not( defined( $state ) ) ) {
		$state -> { 'comments' } = initstate();
		$state -> { 'statements' } = initstate();
	}
	if( not( defined( $state -> { 'comments' } -> { 'depth' } ) ) ) {
		$state -> { 'comments' } = initstate();
	}
	if( not( defined( $state -> { 'statements' } -> { 'depth' } ) ) ) {
		$state -> { 'statements' } = initstate();
	}

	return( undef ) unless( defined( $line ) and length( $line ) );
	if( $line =~ m/^\s*$/ ) {
		pdebug( "  S Skipping blank line '$line' ..." );
		return( undef );
	}

	# Previously, we were looking for lines where the entirity of the line
	# was a hint in order to handle the text as a hint rather than as a
	# comment - however, it transpires that hints can correctly appear
	# within a statement also, so we'll just have to return any hint-like
	# data as-is.  Hopefully this will be safe...
	if( $line =~ m#(^|\s+)/\*![0-9]{5} .+ \*/(\s+|;\s*$)# ) {
		pdebug( "  * Not processing text with hint '$line' for comments ..." );
	} else {
		pdebug( "  * Start processing text '$line' ..." );

		$line = processcomments( $data, $line, $state, $strict );

		return( $line ) unless( defined( $line ) );
	}

	pdebug( "  S Line '$line' should contain a statement..." );

	if( $line =~ m/^\s*delimiter\s+([^\s]+)\s*(.*)$/i ) {
		my $delim = $1;
		$line = $2;

		pdebug( "  * Changing statement delimiter to '$delim' ..." );
		$state -> { 'statements' } -> { 'symbol' } = $delim;

		my $sqlparser = SQLParser -> new();
		my $tokens;
		eval {
			$tokens = $sqlparser -> parse( "DELIMITER $delim" );
		};
		if( $@ ) {
			warn( $@ . "\n" );
			$state -> { 'statements' } -> { 'tokens' } = undef;
		} else {
			$state -> { 'statements' } -> { 'tokens' } = $tokens;
		}

		pushfragment( $state -> { 'statements' }, 'statement', "DELIMITER $delim", 'delimiter change' );
		pushstate( $data, $state -> { 'statements' } );
		$state -> { 'statements' } -> { 'depth' } = 0;
		$state -> { 'statements' } -> { 'line' } = 0;
		undef( $state -> { 'statements' } -> { 'type' } );
		undef( $state -> { 'statements' } -> { 'entry' } );

		return( undef ) unless( length( $line ) );

		if( length( $line ) ) {
			return( processline( $data, $line, $state, $strict ) );
		} else {
			return( undef );
		}
	}

	my $delim = DEFDELIM;
	$delim = $state -> { 'statements' } -> { 'symbol' } if( defined( $state -> { 'statements' } -> { 'symbol' } ) );

	#pdebug( "  S About to split line '$line' into individual items..." );

	# We have an issue where a lone delimiter will cause the entire
	# 'foreach' block below to be skipped, meaning that the statement
	# termianted by the delimiter on a line by itself is never processed.
	# Rather than duplicate a chunk of code for this case, we cheat and add
	# a second delimiter - an entirely safe operation - which causes
	# 'foreach' to process the intervening space character!
	if( $line =~ m/^\s*$delim\s*$/ ) {
		pdebug( "  S Expanding trailing delimiter '$delim'..." );
		$line = $delim . ' ' . $delim;
	}

	foreach my $item ( split( /\Q$delim\E/, $line ) ) {

		#pdebug( "  S Split item '$item' from line '$line'..." );

		if( $line =~ m/^\s*$/ ) {
			pdebug( "  S Skipping blank segment '$line' ..." );
			return( undef );
		}

		# perl didn't like '\s' here...
		my $term = "\Q$item\E[[:space:]]*\Q$delim\E";

		if( $line =~ m/$term/ ) {
			# $item contains a complete SQL statement, or the end
			# of a previously started one...
			#
			my( $pre, $post ) = split( /\Q$delim\E/, $line, 2 );
			$pre =~ s/^\s+//; $pre =~ s/\s+$//;
			$post =~ s/^\s+//; $post =~ s/\s+$//;

			pdebug( "  S Complete or follow-on sections are '$pre' & '$post'" );

			pushfragment( $state -> { 'statements' }, 'statement', ( defined( $pre ) ? $pre : '' ) . $delim, 'SQL ending' );

			#
			# SQL::Parser
			#
			#my $sqlparser = SQL::Parser -> new( 'ANSI' );
			#my $command = join( ' ', @{ $state -> { 'statements' } -> { 'entry' } } );
			#my $tokens;
			#if( $sqlparser -> parse( $command ) ) {
			#	$tokens = $sqlparser -> structure;
			#	$state -> { 'statements' } -> { 'tokens' } = $tokens;
			#} else {
			#	warn( "Failed to parse SQL statement '$command'\n" );
			#}

			#my $command = join( ' ', @{ $state -> { 'statements' } -> { 'entry' } } );
			#my $tokens= SQL::Tokenizer->tokenize( $command, TRUE );
			#$state -> { 'statements' } -> { 'tokens' } = $tokens;

			#
			# Percona SQLParser (included above)
			#
			my $sqlparser = SQLParser -> new();
			my $command = join( ' ', @{ $state -> { 'statements' } -> { 'entry' } } );
			my $tokens;
			if( $command =~ m/^USE\s+`?(.+?)`?$/i ) {
				if( defined( $strict ) and $strict ) {
					die( "$fatal Not parsing prohibited command '$command'" . ( ( defined( $state -> { 'file' } ) and length( $state -> { 'file' } ) ) ? " from file '" . $state -> { 'file' } . "'" : '' ) . "\n" );
				} else {
					warn( "$warning Not parsing prohibited command '$command'" . ( ( defined( $state -> { 'file' } ) and length( $state -> { 'file' } ) ) ? " from file '" . $state -> { 'file' } . "'" : '' ) . "\n" );
				}

			} elsif( $command =~ m/^\s*$delim\s*$/ ) {
				pdebug( "  S Not parsing lone delimiter from '$command', but pushing statements array ..." );
				pushstate( $data, $state -> { 'statements' } );

			} else {
				# We only parse SQL to determine affected
				# tables, so we can make this easier by
				# removing all quoted strings, so that the
				# easily-confused parser is less likely to
				# become flummoxed.
				my @replacements;

				# Handle escaped quotes, which confuse parsing.
				( my $filteredcommand = $command ) =~ s/''/__MW_LITERAL_QUOTE__/g;

				foreach my $match ( ( $filteredcommand =~ m/$RE{ quoted }/g ) ) {
					# $RE{quoted} also captures back-ticks,
					# which we need to maintain...
					next if( $match =~ m/^\`.*\`$/ );

					if( not( length( $match ) > 2 ) ) {
						pdebug( "  S Quoted string `$match` is too short to process - skipping further processing of this token" );
						next;
					}

					my $qu = substr( $match, 0, 1 );
					my $te = substr( $match, -1, 1 );
					if( $qu ne $te ) {
						pdebug( "  S Found differing quoted string delimiters `$qu` and `$te` - skipping further processing string `$match`" );
						next;
					} elsif( not( $qu =~ m/['"]/ ) ) {
						pwarn( "  S Token string delimiter `$qu` is not recognised - skipping further processing string `$match`" );
						next;
					}
					# Keep external quotes...
					$match =~ s/^$qu//;
					$match =~ s/$te$//;

					my $index = scalar( @replacements );
					$filteredcommand =~ s/$qu\Q$match\E$te/${qu}__MW_TOK_${index}__${te}/;
					push( @replacements, $match );
					pdebug( "  S Replacing \`$match\` with \`__MW_TOK_${index}__\` to give \`$filteredcommand\`" );
				}

				eval {
					$tokens = $sqlparser -> parse( $filteredcommand, $delim );
				};
				if( $@ ) {
					( my $errortext = $@ ) =~ s/\.$//;
					chomp( $errortext );

					if( defined( $strict ) and $strict ) {
						if( $errortext =~ m/Cannot parse .* queries/ ) {
							warn( "!> " . $errortext . ( ( defined( $state -> { 'file' } ) and length( $state -> { 'file' } ) ) ? " in file '" . $state -> { 'file' } . "'" : '' ) . "\n" );
							$state -> { 'statements' } -> { 'tokens' } = undef;
						} else {
							die( "\n" . $errortext . ( ( defined( $state -> { 'file' } ) and length( $state -> { 'file' } ) ) ? " in file '" . $state -> { 'file' } . "'" : '' ) . "\n" );
						}
					} else {
						warn( "!> " . $errortext . ( ( defined( $state -> { 'file' } ) and length( $state -> { 'file' } ) ) ? " in file '" . $state -> { 'file' } . "'" : '' ) . "\n" );
						$state -> { 'statements' } -> { 'tokens' } = undef;
					}
				} else {
					sub walk( $$;$ );
					sub walk( $$;$ ) { # {{{
						my ( $element, $block, $vars ) = @_;

						my $type = ref( $element );

						if( 'HASH' eq $type ) {
							walk( $_, $block, $vars ) for( values( %$element ) );
						} elsif( 'ARRAY' eq $type ) {
							walk( $_, $block, $vars ) for( @$element );
						} elsif( ( 'SCALAR' eq $type ) or ( '' eq $type ) ) {
							$block -> ( \$_[ 0 ], $vars );
						} else {
							die "Unknown type '$type'";
						}
					} # walk # }}}
					walk( $tokens, sub {
						my ( $strref, $varref ) = @_;

						return if( not( length( ${ $strref } ) and ( ${ $strref } =~ m/__MW_TOK_/ ) ) );
						#warn "WWW: strref is '$strref', refers to '" . ${ $strref } . "'";

						my @str = @{ $varref };
						#warn "WWW: walk read " . scalar( @str ) . " parameters";
						return if( not( scalar( @str ) ) );

						for( my $index = ( scalar( @str ) - 1 ) ; $index >= 0 ; $index-- ) {
							my $match = $str[ $index ];
							#warn "WWW: walk read original string '$match'";

							if( defined( $match ) and length( $match ) ) {
								my $original = ${ $strref };
								if( ${ $strref } =~ s/__MW_TOK_${index}__/$match/ ) {
									pdebug( "  S Replaced \`__MW_TOK_${index}__\` from tokenised hash leaf value \`$original\` with \`$match\` to give \`${ $strref }\`" );
								} elsif( ${ $strref } =~ s/__MW_LITERAL_QUOTE__/''/ ) {
									pdebug( "  S Replaced \`__MW_LITERAL_QUOTE__\` from tokenised hash leaf value \`$original\` with \`''\` to give \`${ $strref }\`" );
								}
							}
						}
					}, \@replacements );

					$state -> { 'statements' } -> { 'tokens' } = $tokens;
					#print Data::Dumper -> Dump( [ $tokens ], [ qw( *tokens ) ] ) if DEBUG;
				}

				pdebug( "  S Pushing resultant statements array ..." );
				pushstate( $data, $state -> { 'statements' } );
			}
			$state -> { 'statements' } -> { 'depth' } = 0;
			$state -> { 'statements' } -> { 'line' } = 0;
			undef( $state -> { 'statements' } -> { 'type' } );
			undef( $state -> { 'statements' } -> { 'entry' } );

			if( length( $post ) and not( $post eq $delim and not( length( $pre ) ) ) ) {
				pdebug( "  S Follow-on section is '$post'" );

				return( processline( $data, $post, $state, $strict ) )
			} else {
				return( undef );
			}

		} else {
			# $item contains a SQL fragment, which may be the start
			# of a new statement...
			#

			$line =~ s/^\s+//;
			$line =~ s/\s+$//;
			pdebug( "  S New statement or fragment is '$line'" );

			if( 0 == $state -> { 'statements' } -> { 'depth' } ) {
				$state -> { 'statements' } -> { 'type' } = 'statement';
			}
			pushfragment( $state -> { 'statements' }, 'statement', $line, 'SQL statement' );
			return( undef );
		}
	}

	if( length( $line ) ) {
		return( $line );
	} else {
		return( undef );
	}
} # processline # }}}

sub processfile( $$;$$$ ) { # {{{
	my( $data, $file, $marker, $substitution, $strict ) = @_;

	return( undef ) unless( defined( $file ) and length( $file ) and -r $file );

	my $state = initstate();
	my $validated = TRUE;

	$state -> { 'file' } = $file;

	pdebug( "processfile() invoked on file '$file'" );

	open( my $handle, '<:encoding(UTF-8)', $file )
		or die( "$fatal Cannot open '$file' for read: $!\n" );

	LINE: while( my $line = <$handle> ) {
		next LINE unless( length( $line ) );

		chomp( $line );
		$line =~ s/\r$//;

		next LINE unless( length( $line ) );

		if( defined( $marker ) and length( $marker ) ) {
			$substitution = '' unless( defined( $substitution ) and length( $substitution ) );

			my $original = $line;
			if( $line =~ s/$marker/$substitution/ ) {
				print( "!> Substituted '$marker' for '$substitution' in string '$original'\n" );
			}
		}
		# NB: $. contains the last-read line-number
		pdebug( "$. '$line'" );

		$line = processline( $data, $line, $state, $strict );
		next LINE unless( length( $line ) );

		pdebug( "Value '$line' leftover after calling processline()" );
	} # LINE

	close( $handle );

	# It's invalid to leave a dangling statement without a terminating
	# delimiter... but mistakes happen.  Let's try to catch this instance.
	my $count = scalar( @{ $state -> { 'statements'} -> { 'entry' } } ) if( defined( $state -> { 'statements' } -> { 'entry' } ) );
	if( $count ) {
		pwarn( $count . " lines of data are hanging without a delimiter!" );

		my $delim = DEFDELIM;
		$delim = $state -> { 'statements' } -> { 'symbol' } if( defined( $state -> { 'statements' } -> { 'symbol' } ) );
		pwarn( "Attempting to auto-correct by inserting '" . $delim . "' character ..." );

		processline( $data, $delim, $state, $strict );
	}

	# FIXME: We haven't ever actually changed this value since it was defined...
	return( $validated );
} # processfile # }}}

sub dbopen( $$$$;$$ ) { # {{{
	my( $dbh, $dsn, $user, $password, $strict, $options ) = @_;

	my $error = undef;
	$options = { RaiseError => 1, PrintError => 0 } unless( $options );

	#disable diagnostics;
	$$dbh = DBI -> connect( $dsn, $user, $password, $options )
		or $error = "Cannot create connection to DSN '$dsn': $DBI::errstr";
	#enable diagnostics;

	if( defined( $$dbh ) ) {
		$$dbh -> { 'InactiveDestroy' } = 1;

		my $mode = getsqlvalue( $$dbh, 'SELECT @@SESSION.sql_mode' );
		pdebug( "Initial sql_mode is '$mode'" );

		if( $strict ) {
			# If we're not in strict-mode (by the loosest possible
			# definition) then enable it...
			#
			if( $mode !~ m/^.*,?(((STRICT_ALL_TABLES|STRICT_TRANS_TABLES),.*(STRICT_ALL_TABLES|STRICT_TRANS_TABLES))|TRADITIONAL),?.*$/i ) {
				$mode .= ( defined( $mode ) and length ( $mode ) ? ',' : '' ) . "TRADITIONAL";
				dosql( $$dbh, "SET SESSION sql_mode = '$mode'" );
			}

			# Now that we we have an (expanded) sql_mode set, remove
			# the problematic NO_ZERO_DATE option...
			#
			$mode = getsqlvalue( $$dbh, 'SELECT @@SESSION.sql_mode' );
			( my $newmode = $mode ) =~ s/,?NO_ZERO_DATE,?/,/i;
			$newmode =~ s/,?TRADITIONAL,?/,/i;
			$newmode =~ s/^,//;
			$newmode =~ s/,$//;
			dosql( $$dbh, "SET SESSION sql_mode = '$newmode'" ) unless( $mode eq $newmode );

			# Also set InnoDB strict mode - which, thankfully, is
			# somewhat less complex...
			#
			$mode = getsqlvalue( $$dbh, 'SELECT @@SESSION.innodb_strict_mode' );
			if( not( defined( $mode ) ) or ( $mode eq 0 ) ) {
				dosql( $$dbh, "SET SESSION innodb_strict_mode = ON" );
			}
		} else {
			# We actually probably do need to deal with this
			# eventuality - what happens if strict mode is already
			# set?

			# Clear all modes, but only if a strict setting is
			# detected.
			#
			# XXX: It would be better to filter this list with more
			#      granularity...
			#
			if( $mode =~ m/^.*,?(((STRICT_ALL_TABLES|STRICT_TRANS_TABLES),.*(STRICT_ALL_TABLES|STRICT_TRANS_TABLES))|TRADITIONAL),?.*$/i ) {
				dosql( $$dbh, "SET SESSION sql_mode = ''" );
			}
			$mode = getsqlvalue( $$dbh, 'SELECT @@SESSION.innodb_strict_mode' );
			if( $mode eq 1 ) {
				dosql( $$dbh, "SET SESSION innodb_strict_mode = OFF" );
			}
		}

		if( DEBUG or ( $verbosity > 2 ) ) {
			my $mode = getsqlvalue( $$dbh, 'SELECT @@SESSION.sql_mode' );
			pdebug( "Updated sql_mode is '$mode'" );
		}
	}

	return( $error );
} # dbopen # }}}

sub dbclose( ;$$ ) { # {{{
	my( $dbh, $message ) = @_;

	$message = "Complete" unless( defined( $message ) and length( $message ) );

	if( defined( $dbh ) and $dbh ) {
		print( "\n=> $message - disconnecting from database ...\n" );
		$dbh -> disconnect;
	}

	my( $sec, $min, $hour, $mday, $mon, $year, $wday, $yday, $isdst ) = localtime( time );
	$year += 1900;
	printf( "\n=> %s finished at %04d/%02d/%02d %02d:%02d.%02d\n\n", $0, $year, $mon, $mday, $hour, $min, $sec );

	return( TRUE );
} # dbclose # }}}

sub dbdump( $;$$$$$ ) { # {{{
	my( $auth, $objects, $destination, $filename, $compress, $transactional ) = @_;

	# N.B.: If per-table or per-database output is required, then call
	#       dbdump() multiple times with different $objects and
	#       $destination...
	#

	return( undef ) unless( defined( $auth -> { 'user' } ) and length( $auth -> { 'user' } ) );
	return( undef ) unless( defined( $auth -> { 'password' } ) and length( $auth -> { 'password' } ) );
	return( undef ) unless( defined( $auth -> { 'host' } ) and length( $auth -> { 'host' } ) );

	my $user =     $auth -> { 'user' };
	my $password = $auth -> { 'password' };
	my $host =     $auth -> { 'host' };

	my $port;
	$port = $auth -> { 'port' } if( defined( $auth -> { 'port' } ) and $auth -> { 'port' } );
	$port = PORT unless( defined( $port ) and $port );

	my $memorybackend;

	if( defined( $filename ) and length( $filename ) and -d $filename and ( not( defined( $destination ) ) or not( length( $destination ) ) ) ) {
		$destination = $filename;
		$filename = undef;
	}
	if( defined( $filename ) and length( $filename ) ) {
		if( defined( $destination ) and length( $destination ) ) {
			if( not( -d $destination ) ) {
				make_path( $destination, {
					  mode		=> 0775
					, verbose	=> FALSE
					, error		=> \my $errors
				} );
				if( @{ $errors } ) {
					foreach my $entry ( @{ $errors } ) {
						my( $dir, $message ) = %{ $entry };
						if( length( $message ) ) {
							print STDERR "Error creating directory '$dir': $message";
						} else {
							print STDERR "make_path general error: $message";
						}
					}
					return( undef );
				}
			}
		}
	} elsif( defined( $destination) and ( '' eq ref( $destination ) ) and length( $destination ) ) {

		# Destination is specified and is a string, presumably a
		# file-path...
		#
		if( -f $destination ) {
			( $filename, $destination ) = fileparse( $destination );
		} elsif( not( -d $destination ) ) {
			make_path( $destination, {
				  mode		=> 0775
				, verbose	=> FALSE
				, error		=> \my $errors
			} );
			if( @{ $errors } ) {
				foreach my $entry ( @{ $errors } ) {
					my( $dir, $message ) = %{ $entry };
					if( length( $message ) ) {
						print STDERR "Error creating directory '$dir': $message";
					} else {
						print STDERR "make_path general error: $message";
					}
				}
				return( undef );
			}
		}
	} elsif( 'SCALAR' eq ref( $destination ) ) {

		# Destination is a string-var into which we should read the
		# database dump...
		# Beware memory requirements of large dumps!
		#
		$memorybackend = $destination;

	} elsif( 'ARRAY' eq ref( $destination ) ) {

		# Destination is an array-var into which we should read the
		# lines of the database dump...
		# Beware memory requirements of large dumps!
		#
		$memorybackend = $destination;

	} else {

		# Without a destination specified, we create an output file in
		# the current directory...
		#
		$destination = realpath( getcwd() );
	}

	my $optdb = '';
	my $opttab = '';
	if( defined( $auth -> { 'database' } ) and length( $auth -> { 'database' } ) ) {

		# We know the database we're concerned with, so $objects gives
		# us the tables to backup...
		#
		$filename = $auth -> { 'database' } . ".sql" unless( defined( $filename ) and length( $filename ) );

		if( not( defined( $objects ) and length( $objects ) ) ) {
			$opttab = '';

		} elsif( ( '' eq ref( $objects ) ) or ( 'SCALAR' eq ref( $objects ) ) ) {
			$opttab = $objects;

		} elsif( 'ARRAY' eq ref( $objects ) ) {
			$opttab = '';
			foreach my $item ( @{ $objects } ) {
				$opttab .= " $item"
			}

		} elsif( 'HASH' eq ref( $objects ) ) {
			die( "Unsupported reference type 'HASH' for table parameter \$objects\n" );

		} else {
			die( "Unknown reference type '" . ref( $objects ) . "' for table parameter \$objects\n" );
		}

		# mysqldump accepts '<database> [tables]' or
		# '--databases <databases>', but not a combination of the two...
		#
		if( defined( $auth -> { 'database' } ) and length( $auth -> { 'database' } ) ) {
		#	if( not( length( $opttab ) ) ) {
		#		$optdb = '--databases ' . $auth -> { 'database' };
		#	} else {
				$optdb = $auth -> { 'database' };
		#	}
		}
	} else {

		# We've not defined a database to backup, therefore $objects
		# contains a list of databases...
		#
		$opttab = '';

		if( not( defined( $objects ) and length( $objects ) ) ) {
			$optdb = "--all-databases";

		} elsif( ( '' eq ref( $objects ) ) or ( 'SCALAR' eq ref( $objects ) ) ) {
			$optdb = "--databases $objects"

		} elsif( 'ARRAY' eq ref( $objects ) ) {
			$optdb = "--databases";
			foreach my $item ( @{ $objects } ) {
				$optdb .= " $item"
			}

		} elsif( 'HASH' eq ref( $objects ) ) {
			die( "Unsupported reference type 'HASH' for database parameter \$objects\n" );

		} else {
			die( "Unknown reference type '" . ref( $objects ) . "' for database parameter \$objects\n" );
		}

		if( '' eq ref( $destination ) ) {
			if( not( defined( $filename ) and length( $filename ) ) ) {
				my $default = 'dump.sql';

				if( -e $destination . '/'. $default ) {
					die( "dbdump: No output filename specified and '$default' already exists\n" );
				} else {
					pwarn( "dbdump: No output filename specified - using '$default'" );
					$filename = $default;
				}
			}
		}
	}

	my $optauth = "\"--user=$user\" \"--password=$password\" \"--host=$host\"";
	my $optdump;

	# TODO: Support Stored Procedure-only backups:
	# if( 'procedure' eq $mode ) {
	# 	$optdump = '--skip-opt -no-create-info --no-data'
	# 		 . '--no-create-db --routines';
	# } else
	if( defined( $transactional ) and $transactional ) {
		$optdump = '--skip-opt --add-drop-database --add-drop-table'
			 . ' --add-locks --allow-keywords --comments'
			 . ' --complete-insert --create-options'
			 . ' --disable-keys --dump-date --events --flush-logs'
			 . ' --flush-privileges --hex-blob'
			 . ' --include-master-host-port --no-autocommit'
			 . ' --order-by-primary --quote-names'
			 . ' --routines --set-charset --single-transaction'
			 . ' --triggers --tz-utc'
			 ;
	} else {
		$optdump = '--skip-opt --add-drop-database --add-drop-table'
			 . ' --add-locks --allow-keywords --comments'
			 . ' --complete-insert --create-options'
			 . ' --disable-keys --dump-date --events --flush-logs'
			 . ' --flush-privileges --hex-blob'
			 . ' --include-master-host-port --lock-all-tables'
			 . ' --order-by-primary --quick --quote-names'
			 . ' --routines --set-charset --triggers --tz-utc'
			 ;
		# Let's assume that if we're doing a full backup in this way,
		# then we're either backing up from a master node, or that this
		# behaviour is likely what we need regardless...
		#
		# --master-data: Write binary log name and position to output;
		# --dump-slave:  Include CHANGE MASTER statement that provides
		#                master log position.
		#
		# By using argument '2' the CHANGE MASTER command is commented,
		# allowing tracking of where the backup was taken from without
		# mandating restoration to a slave.
		#
		print( "\n=> Checking Master status of database on '$host' ...\n" );
		my $dsn = "DBI:mysql:host=$host;port=$port";
		my $dbh;
		my $error = dbopen( \$dbh, $dsn, $user, $password, FALSE );
		die( $error ."\n" ) if $error;

		my $master = getsqlvalue( $dbh, 'SELECT @@log_bin' );

		print( "\n=> Complete - disconnecting from database ...\n" );
		$dbh -> disconnect;

		if( 1 == $master ) {
			print( "\n*> Database has bin-logging enabled - adding '--master-data' option\n" );

			$optdump .= ' --master-data=2';
			#$optdump .= ' --dump-slave=2';

			# N.B. The '--gtid' option is present in MariaDB mysqldump
			#      10.0.13 and above only (although earlier 10.1.x versions
			#      may also lack the option...)
			if( qx( mysqldump --version ) =~ m/ Distrib ([^-,]+)[-,]/ ) {
				my @sortedversions = sort { versioncmp( $a, $b ) } ( $1, '10.0.12' );
				my $latest = pop( @sortedversions );
				if( not( $latest eq '10.0.12' )  ) {
					print( "\n*> mysqldump supports Global Transaction IDs - adding '--gtid' option\n" );
					$optdump .= ' --gtid';
				}
			}
		}
	}
	if( defined( $verbosity ) and ( $verbosity > 0 ) ) {
		$optdump .= ' --verbose';
	}

	my $msg = 'Commencing database backup';
	$msg .= ' - there may be a delay while a GLOBAL READ LOCK is obtained' if( not( $transactional ) );
	print( "\n=> " . $msg . " ...\n" );
	print( "\n!> Passing control to 'mysqldump' from this point onwards.\n\n" );

	# N.B.: We're not capturing STDERR in either instance...
	#
	if( not( defined( $memorybackend ) ) ) {
		my $output = ( defined( $destination ) and length( $destination ) ? $destination . '/' : '' ) . $filename;
		my $command = "mysqldump $optauth $optdb $opttab $optdump ";
		$command = "strace -vvfFtTs 128 -o \"${output}.strace\" $command" if( DEBUG );

		if( defined( $compress ) and length( $compress ) ) {
			if( 'gzip' eq $compress ) {
				$output .= '.gz';
				$command .= " | gzip -9cf - > \"$output\"";
			} elsif( ( 'lzma' eq $compress ) or ( 'xz' eq $compress ) ) {
				$output .= '.' . $compress;
				$command .= " | $compress -z6cf - > \"$output\"";
			} elsif( ( 'bzip2' eq $compress ) or ( '' eq $compress ) ) {
				$output .= '.bz2';
				$command .= " | bzip2 -z9cf - > \"$output\"";
			} else {
				die( "Unknown compression scheme '$compress'\n" );
			}
		} else {
			$command .= "--result-file=\"$output\"";
		}
		eval {
			touch( $output );
		};
		if( $@ ) {
			die( "$fatal $@\n" );
		}

		pdebug( "Shell-command is: '$command'" );
		my $result = qx( $command );
		if( not( defined( $result ) ) ) {
			warn( "Unable to launch external process: $!\n" );
			return( undef );
		}
		if( $? ) {
			warn( "Database dump failed: $?\n" ) ;
			return( undef );
		}
		#return( $result );
		return( TRUE );

	} elsif( ( 'SCALAR' eq ref( $memorybackend ) ) or ( 'ARRAY' eq ref( $memorybackend ) ) ) {
		pdebug( "Shell-command is: 'mysqldump $optauth $optdb $opttab $optdump'" );
		$memorybackend = qx/ mysqldump $optauth $optdb $opttab $optdump /;
		if( not( defined( $memorybackend ) ) ) {
			return( undef );
		} else {
			return( TRUE );
		}
	}

	# Unreachable
	return( undef );
} # dbdump # }}}

sub dbrestore( $$ ) { # {{{
	my( $auth, $file ) = @_;

	return( undef ) unless( defined( $auth -> { 'user' } ) and length( $auth -> { 'user' } ) );
	return( undef ) unless( defined( $auth -> { 'password' } ) and length( $auth -> { 'password' } ) );
	return( undef ) unless( defined( $auth -> { 'host' } ) and length( $auth -> { 'host' } ) );
	return( undef ) unless( defined( $file ) );

	my $user = $auth -> { 'user' };
	my $password = $auth -> { 'password' };
	my $host = $auth -> { 'host' };

	my $mysql = which( 'mysql' );

	die( "Cannot locate 'mysql' binary\n" ) unless( defined( $mysql ) and -x $mysql );
	die( "Cannot read file '$file'\n" ) unless( -r $file );

	# To resolve bugs.mysql.com/69970, any instance of:
	#
	#   /*!40000 DROP DATABASE IF EXISTS `mysql`*/;
	#
	# needs to be replaced with:
	#
	#   /*!50106 SET @OLD_GENERAL_LOG=@@GENERAL_LOG*/;
	#   /*!50106 SET GLOBAL GENERAL_LOG=0*/;
	#   /*!50106 SET @OLD_SLOW_QUERY_LOG=@@SLOW_QUERY_LOG*/;
	#   /*!50106 SET GLOBAL SLOW_QUERY_LOG=0*/;
	#   /*!40000 DROP DATABASE IF EXISTS `mysql`*/;
	#   /*!50106 SET GLOBAL GENERAL_LOG=@OLD_GENERAL_LOG*/;
	#   /*!50106 SET GLOBAL SLOW_QUERY_LOG=@OLD_SLOW_QUERY_LOG*/;
	#

	my $decompress;
	if( $file =~ /\.bz2$/ ) {
		$decompress = 'bunzip2 -cdq';
	} elsif( $file =~ /\.gz$/ ) {
		$decompress = 'gunzip -cq';
	} elsif( $file =~ /\.xz$/ ) {
		$decompress = 'unxz -cdq';
	} elsif( $file =~ /\.lzma$/ ) {
		$decompress = 'unlzma -cdq';
	}
	pdebug( "Will decompress data with command '$decompress'" ) if( defined( $decompress) and length( $decompress ) );

	my $command;
	if( which( 'pv' ) ) {
		my ( $columns, $rows );
		$columns = $rows = '';
		if( defined( $ENV{ 'COLUMNS' } ) and $ENV{ 'COLUMNS' } ) {
			$columns = ' -w ' . $ENV{ 'COLUMNS' };
		}
		if( defined( $ENV{ 'LINES' } ) and $ENV{ 'LINES' } ) {
			$rows = ' -H ' . $ENV{ 'LINES' };
		}
		$command = 'pv -e -p -t -r -a -b -c ' . $columns . $rows . ' -N "' . basename( $file ) . '" "' . $file . ( defined( $decompress ) ? '" | ' . $decompress : '"' ) . ' | { ' . $mysql . " -u $user -p$password -h $host 2>&1 ; }"
	} else {
		warn( "$warning Cannot locate 'pv' executable: only errors will be reported\n\n" );

		$command = 'cat "' . basename( $file ) . '" "' . $file . ( defined( $decompress ) ? '" | ' . $decompress : '"' ) . ' | { ' . $mysql . " -u $user -p$password -h $host 2>&1 ; }"
	}
	pdebug( "Restore command is '$command'" );
	exec( $command ) or die( "Failed to execute 'pv' in order to monitor data restoration: $!\n" );

	# Unreachable
	return( undef );
} # dbrestore # }}}

sub dosql( $$ ) { # {{{
	my( $dbh, $st ) = @_;

	return( undef ) unless( defined( $dbh ) );
	#eval {
	#	my $state = $dbh -> state();
	#	die( $@ ) unless( defined( $state ) and ( '00000' eq $state ) );
	#};
	#if( $@ ) {
	#	die( "Not a database handle or handle state in error: $@" );
	#}
	return( undef ) unless( defined( $st ) and length( $st ) );

	pdebug( "SQL: Sending to database: \"$st\"" );
	eval {
		my $result = $dbh -> do( $st );

		# We're now seeing 'CREATE TABLE IF NOT EXISTS' throwing a
		# warning, and then we abort with 'MySQL server has gone away'
		# ... which is weird :(
		#
		# Update: Setting 'InactiveDestroy' on $dbh seems to resolve
		#         this by enabling auto-reconnect.
		#
		if( not( defined( $result ) ) ) {
			#die( "Error when processing SQL statement:\n$st\n" );
			die( $dbh -> errstr() . "\n" );
		}
	};
	if( $@ ) {
		warn( "\nError when processing SQL statement (" . $dbh -> err() . "):\n$st\n$@" );
		if( ( ( $st =~ m/^\s*DROP\s/i ) or ( $st =~ m/^\s*ALTER\s(O(N|FF)LINE\s+)?(IGNORE\s+)?TABLE\s.*\sDROP\s/i ) ) and $dbh -> err() eq '1091' ) {
			# XXX: This simply seems to propagate the error to the
			#      next prepared statement, which will then fail.
			#
			#
			# If we're trying to DROP an item which doesn't exist,
			# then arguably the desired state has been reached, so
			# we shouldn't abort...
			my $lasterr = $dbh -> err();
			$dbh -> set_err( undef, undef );

			# XXX: Do we break after the following statement, even
			#      though the error should have been cleared?
			if( not( dosql( $dbh, "SELECT '(Encountered error $lasterr)'" ) ) ) {
				die( "Trivial command following error failed" );
			}

			return( TRUE );

		} else {
			return( FALSE );
		}
	} else {
		return( TRUE );
	}

	# Unreachable
	return( undef );
} # dosql # }}}

sub preparesql( $$ ) { # {{{
	my( $dbh, $st ) = @_;

	return( undef ) unless( defined( $dbh ) );
	#eval {
	#	my $state = $dbh -> state();
	#	die( $@ ) unless( defined( $state ) and ( '00000' eq $state ) );
	#};
	#if( $@ ) {
	#	die( "Not a database handle or handle state in error: $@" );
	#}
	return( undef ) unless( defined( $st ) and length( $st ) );

	pdebug( 'SQL: Preparing: "' . join( ' ', split( /\s*\n\s*/, $st ) ) . '"' );
	my $sth = $dbh -> prepare_cached( $st );
	if( $@ ) {
		my $error = $dbh -> errstr();
		warn( "\nError when processing SQL statement:\n$st\n$@\n" . ( defined( $error ) and length( $error) ? $error . "\n" : '' ) );
		return( undef );
	} else {
		# N.B.: $sth -> finish() must be called prior to the next SQL
		#       interaction!

		return( $sth );
	}

	# Unreachable
	return( undef );
} # preparesql # }}}

sub executesql( $$$;@ ) { # {{{
	my( $dbh, $sth, $st, @values ) = @_;

	return( undef ) unless( defined( $dbh ) );
	#eval {
	#	my $state = $dbh -> state();
	#	die( $@ ) unless( defined( $state ) and ( '00000' eq $state ) );
	#};
	#if( $@ ) {
	#	die( "Not a database handle or handle state in error: $@" );
	#}
	if( not( defined( $sth ) and $sth ) ) {
		return( undef ) unless( defined( $st ) and length( $st ) );
		$sth = preparesql( $dbh, $st );
		return( undef ) unless( defined( $sth ) and $sth );
	}

	pdebug( 'SQL: Executing: "' . join( ' ', split( /\s*\n\s*/, $dbh -> { 'Statement' } ) ) . '"' ) if( defined( $dbh -> { 'Statement' } ) );
	pdebug( 'SQL: Parameters: "' . join( '", "', grep defined, @values ) . '"' ) if( @values and scalar( @values ) );
	eval {
		my $result = $sth -> execute( @values );
		if( not( defined( $result ) ) ) {
			#die( "Error when processing SQL statement:\n$st\n" );
			die( $dbh -> errstr() . "\n" );
		}
	};
	if( $@ ) {
		my $errstr = $@;

		my $stherr = $sth -> err if( defined( $sth -> err ) );
		my $stherrstr = $sth -> errstr if( defined( $sth -> errstr ) );
		my $sthstate = $sth -> state if( defined( $sth -> state ) );

		eval {
			$sth -> finish();
		};
		$sth = undef;

		@values = map { defined( $_ ) ? $_ : '' } @values;

		if( defined( $st ) ) {
			warn( "\nError when processing SQL statement:\n$st\n" );
			warn( '... with parameters "' . join( '", "', @values ) . "\"\n" ) if( scalar( @values ) );
		} else {
			warn( 'Error applying parameters "' . join( '", "', @values ) . "\"\n" ) if( @values and scalar( @values ) );
		}
		warn( "Error was:\n" );
		warn( $errstr . "\n" );
		warn( $dbh -> errstr() . "\n" ) if( defined( $dbh -> errstr() ) );
		warn( "Statement debug:\n" );
		warn( $stherr . "\n" ) if( defined( $stherr ) );
		warn( $stherrstr . "\n" ) if( defined( $stherrstr ) );
		warn( $sthstate . "\n" ) if( defined( $sthstate ) );

		return( undef );

	} else {
		# N.B.: $sth -> finish() must be called prior to the next SQL
		#       interaction!

		return( $sth );
	}

	# Unreachable
	return( undef );
} # executesql # }}}

sub getsqlvalue( $$ ) { # {{{
	my( $dbh, $st ) = @_;

	return( undef ) unless( defined( $dbh ) );
	#eval {
	#	my $state = $dbh -> state();
	#	die( $@ ) unless( defined( $state ) and ( '00000' eq $state ) );
	#};
	#if( $@ ) {
	#	die( "Not a database handle or handle state in error: $@" );
	#}
	return( undef ) unless( defined( $st ) and length( $st ) );

	my $response;

	my $sth = executesql( $dbh, undef, $st );
	if( not( defined( $sth ) and $sth ) ) {
		my $errstr = $dbh -> errstr();
		warn( "Unable to create statement handle to execute '$st'" . ( defined( $errstr ) and length( $errstr ) ? ": " . $errstr : '' ) . "\n" );
	} else {
		while( my $ref = $sth -> fetchrow_arrayref() ) {
			$response = @{ $ref }[ 0 ];
		}
		$sth -> finish();
	}

	return( $response );
} # getsqlvalue # }}}

sub getsqlvalues( $$;$ ) { # {{{
	my( $dbh, $st, $column ) = @_;

	return( undef ) unless( defined( $dbh ) );
	#eval {
	#	my $state = $dbh -> state();
	#	die( $@ ) unless( defined( $state ) and ( '00000' eq $state ) );
	#};
	#if( $@ ) {
	#	die( "Not a database handle or handle state in error: $@" );
	#}
	return( undef ) unless( defined( $st ) and length( $st ) );

	$column = 0 unless( defined( $column ) and ( $column =~ m/^\d+$/ ) and ( $column >= 0 ) );

	my @response;

	my $sth = executesql( $dbh, undef, $st );
	if( defined( $sth ) and $sth ) {
		while( my $ref = $sth -> fetchrow_arrayref() ) {
			push( @response, @{ $ref }[ $column ] );
		}
		$sth -> finish();
	} else {
		warn( "Unable to create statement handle to execute '$st': " . $dbh -> errstr() . "\n" );
	}

	return( \@response );
} # getsqlvalues # }}}

sub outputtable( $$;$ ) { # {{{
	my( $dbh, $st, $fh ) = @_;


	my $sth = executesql( $dbh, undef, $st );
	if( defined( $sth ) and $sth ) {
		my $table = DBI::Format::PartBox -> new();
		if( defined( $fh ) ) {
			$table -> header( $sth, $fh );
		} else {
			$table -> header( $sth );
		}
		while( my $ref = $sth -> fetchrow_arrayref() ) {
			$table -> row( $ref );
		}
		$table -> trailer();
		$sth -> finish();
	} else {
		warn( 'Unable to create statement handle to render table' . ( defined( $dbh -> errstr() ) ? ': ' . $dbh -> errstr() : '' ) . "\n" );
	}

	return( TRUE );
} # outputtable # }}}

sub formatastable( $$$ ) { # {{{
	my( $dbh, $st, $indent ) = @_;

	return( undef ) unless( defined( $dbh ) );
	return( undef ) unless( defined( $st ) and length( $st ) );
	$indent = '' unless( defined( $indent ) and length( $indent ) );

	my( $read, $write ) = FileHandle::pipe;

	# If we're writing more than 8k(?) of data, the pipe will block until
	# it is read from and drained... but in the code below, this only
	# happens once the table is fully written, resulting in a deadlock :(
	#
	my $firstchildpidorzero = fork;
	die( "fork() failed: $!\n" ) unless( defined( $firstchildpidorzero ) );

	if( 0 == $firstchildpidorzero ) {
		# Child process

		# Will likely fail on non-UNIX systems - perlport(1) declares
		# 'setpgrp' as unimplemented on 'Win32, VMS, RISC OS, VOS'.
		#
		eval {
			setpgrp( 0, 0 );
		};

		$read -> close();

		# We'll output the table (to our pipe) in the child process, so
		# that the parent retains all I/O.
		#
		outputtable( $dbh, $st, $write );
		$write -> close();

		exit( 0 );
	} else {
		# Parent process

		$write -> close();

		while( my $line = $read -> getline() ) {
			chomp( $line );
			print( $indent . $line . "\n" );
		}
		$read -> close();

		if( waitpid( $firstchildpidorzero, 0 ) > 0 ) {
			my( $rc, $sig, $core ) = ( $? >> 8, $? & 127, $? & 128 );

			if( $core ) {
				warn( "$fatal rendering process $firstchildpidorzero core-dumped\n" );
			} elsif( 9 == $sig ) {
				warn( "$warning rendering process $firstchildpidorzero was KILLed\n" );
			} else {
				pwarn( "rendering process $firstchildpidorzero returned $rc" . ( $sig ? " after signal $sig" : '' ) ) unless( 0 == $rc );
			}
		} else {
			pwarn( "backup process $firstchildpidorzero disappeared" );
		}
	}

	return( TRUE );
} # formatastable # }}}

sub applyschema( $$$$;$ ) { # {{{
	my ( $file, $actions, $variables, $auth, $schmvirtual ) = @_;

	return( FALSE ) unless( ref( $actions ) eq 'HASH' );
	return( FALSE ) unless( ref( $variables ) eq 'HASH' );
	return( FALSE ) unless( not( defined( $schmvirtual ) ) or ( ( ref( $schmvirtual ) eq '' ) or ( ref( $schmvirtual ) eq 'SCALAR' ) ) );
	$schmvirtual = ${ $schmvirtual } if( ref( $schmvirtual ) eq 'SCALAR' );

	# TODO: Value written to metadata table on success
	my $status = 0;

	#
	# Retrieve variable and settings values # {{{
	#

	my ( $action_init, $action_migrate, $action_check );
	$action_init    = $actions -> { 'init' }    if( exists( $actions -> { 'init' } ) );
	$action_migrate = $actions -> { 'migrate' } if( exists( $actions -> { 'migrate' } ) );
	$action_check   = $actions -> { 'check' }   if( exists( $actions -> { 'check' } ) );

	my( $tmpdir, $mode, $marker, $first, $backupdir, $safetyoff, $strict, $unsafe, $desc, $pretend, $clear, $compat, $force );
	$mode      = $variables -> { 'mode' }      if( exists( $variables -> { 'mode' } ) );
	$marker    = $variables -> { 'marker' }    if( exists( $variables -> { 'marker' } ) );
	$first     = $variables -> { 'first' }     if( exists( $variables -> { 'first' } ) );
	$backupdir = $variables -> { 'backupdir' } if( exists( $variables -> { 'backupdir' } ) );
	$clear     = $variables -> { 'clear' }     if( exists( $variables -> { 'clear' } ) );
	$compat    = $variables -> { 'compat' }    if( exists( $variables -> { 'compat' } ) );
	$desc      = $variables -> { 'desc' }      if( exists( $variables -> { 'desc' } ) );
	$force     = $variables -> { 'force' }     if( exists( $variables -> { 'force' } ) );
	$pretend   = $variables -> { 'pretend' }   if( exists( $variables -> { 'pretend' } ) );
	$safetyoff = $variables -> { 'safetyoff' } if( exists( $variables -> { 'safetyoff' } ) );
	$strict    = $variables -> { 'strict' }    if( exists( $variables -> { 'strict' } ) );
	$tmpdir    = $variables -> { 'tmpdir' }    if( exists( $variables -> { 'tmpdir' } ) );
	$unsafe    = $variables -> { 'unsafe' }    if( exists( $variables -> { 'unsafe' } ) );

	my( $user, $pass, $host, $port, $db );
	$user = $auth -> { 'user' }       if( exists( $auth -> { 'user' } ) );
	$pass = $auth -> { 'password' }   if( exists( $auth -> { 'password' } ) );
	$host = $auth -> { 'host' }       if( exists( $auth -> { 'host' } ) );
	$port = $auth -> { 'port' }       if( exists( $auth -> { 'port' } ) );
	$db   = $auth -> { 'database'   } if( exists( $auth -> { 'database' } ) );

	#
	# Perform additional validation
	#

	$first = FALSE unless( defined( $first ) and $first );

	my( $schmfile, $schmpath, $schmext, $filetype );
	if( not( defined( $file ) and length( $file ) ) ) {
		if( defined( $action_init ) ) {
			if( not( length( $action_init ) ) ) {
				die( "$fatal --init requires a parameter: Initial version not specified\n" );
			} elsif( ( -d $action_init ) or ( -r $action_init ) ) {
				if( $force ) {
					warn( "!> Initial version '$action_init' looks like a filesystem object - force-continuing\n" );
				} else {
					if( $pretend ) {
						warn( "!> Initial version '$action_init' looks like a filesystem object - would abort unless forced\n" );
					} else {
						die( "$fatal Initial version '$action_init' looks like a filesystem object - re-run with '--force' to proceed regardless\n" );
					}
				}
			} elsif( $action_init =~ m/^--/ ) {
				if( $force ) {
					warn( "!> Initial version '$action_init' looks like a follow-on argument - force-continuing\n" );
				} else {
					if( $pretend ) {
						warn( "!> Initial version '$action_init' looks like a follow-on argument - would abort unless forced\n" );
					} else {
						die( "$fatal Initial version '$action_init' looks like a follow-on argument - re-run with '--force' to proceed regardless\n" );
					}
				}
			}
		} else {
			die( "$fatal File name required\n" );
		}
	} else {
		die( "$fatal Cannot read from file '$file'\n" ) unless( defined( $file ) and -r $file );

		( $schmfile, $schmpath, $schmext ) = fileparse( realpath( $file ), qr/\.[^.]+/ );
		if( not( defined( $desc ) and length( $desc ) ) ) {
			if( $schmfile =~ m/^V.*?__(.*?)(?:\.d[dm]l)?$/ ) {
				( $desc = $1 ) =~ s/_/ /g;
			}
		}
		$desc = 'No description' unless( defined( $desc ) and length( $desc ) );
		if( defined( $schmext ) and length( $schmext ) ) {
			$filetype = uc( $schmext );
			$filetype =~ s/\.//;
		} else {
			$filetype = 'Unknown';
		}
		$schmfile = $schmfile . $schmext;
	}

	# }}}

	#
	# Tokenise and parse SQL statements from $file
	#

	my $schmversion = $action_init;
	$schmversion = $1 if( not( defined( $schmversion ) and length( $schmversion ) ) and ( $schmfile =~ m/^V(.*?)__/ ) );
	$schmversion = '0' unless( defined( $schmversion ) and length( $schmversion ) );

	my $metadata = {};
	my $procedureversion;
	my $data = {};
	my $invalid = FALSE;
	my $dumpusers = FALSE;
	my @dumptables = ();

	if( 'procedure' eq $mode ) {
		if( defined( $marker ) and length( $marker ) ) {
			$procedureversion = $1 if( dirname( $file ) =~ m/^(?:.*?)(_v\d+_\d+)$/ );
			if( defined( $procedureversion ) ) {
				$procedureversion .= '` ';
				if( $pretend ) {
					print( "*> Would adjust Stored Procedure names with version string '$procedureversion'\n" );
				} else {
					print( "*> Will adjust Stored Procedure names with version string '$procedureversion'\n" );
				}
			} else {
				if( $force ) {
					warn( "!> Cannot determine Stored Procedure version string - removing versioning\n" );
				} else {
					if( $pretend ) {
						warn( "!> Cannot determine Stored Procedure version string - would abort unless forced\n" );
					} else {
						die( "$fatal Cannot determine Stored Procedure version string from directory '" . dirname( $file ) . "' - aborting\n" );
					}
				}
			}
		}

		# In this case, we retrieve the previous/current-version logic
		# from the metadata file, and many files may be applied with
		# the same versions.
		my $metafile = dirname( $file ) . '/' . $db . '.metadata';
		die( "Cannot read metadata '$db.metadata' for file '$file'\n" ) unless( -s $metafile );
		print( "*> Using metadata file '$metafile'\n" );

		$invalid = $invalid | not( processfile( $metadata, $metafile, undef, undef, $strict ) );
		die( "Metadata failed validation - aborting.\n" ) if( $invalid );

		my $okay = TRUE;
		foreach my $entry ( $metadata -> { 'entries' } ) {
			foreach my $statement ( @{ $entry } ) {
				if( $okay and not( 'comment' eq $statement -> { 'type' } ) ) {
					$okay = FALSE;
					warn( "!> Metadata contains non-comment code which will be executed for each file\n" );
				}
			}
		}
	}

	if( ( 'procedure' eq $mode ) and defined( $marker ) and length( $marker ) ) {
		$invalid = $invalid | not( processfile( $data, $file, $marker, $procedureversion, $strict ) );
	} else {
		$invalid = $invalid | not( processfile( $data, $file, undef, undef, $strict ) );
	}
	die( "Data failed validation - aborting.\n" ) if( $invalid );

	#
	# Confirm data validity, and enumerate tables we need to backup # {{{
	#

	my $output;
	if( $pretend ) {
		$output = \&pfatal;
	} else {
		if( defined( $verbosity ) and $verbosity > 0 ) {
			$output = \&pwarn;
		} else {
			$output = \&pdebug;
		}
	}

	my $statements = 0;
	foreach my $entry ( @{ $data -> { 'entries' } } ) {
		if( not( 'HASH' eq ref( $entry ) ) ) {
			print( "\$entry has unexpected type " .ref( $entry ) . "\n" );
			$invalid = TRUE;
		} else {
			next unless( defined( $entry -> { 'type' } ) );
			next unless( 'statement' eq lc( $entry -> { 'type' } ) );

			#print Dumper $entry if( DEBUG );

			if( not( defined( $entry -> { 'entry' } ) ) ) {
				$output -> ( 'Unable to parse blank entry' );
				$invalid = TRUE;
				next;

			} else {
				my $text;
				my $texttype = ' ';
				if( 'ARRAY' eq ref( $entry -> { 'entry' } ) ) {
					$text = join( ' ', @{ $entry -> { 'entry' } } );
					$texttype = 'array ';
				} else {
					$text = $entry -> { 'entry' };
				}
				$text =~ s/^\s+//g; $text =~ s/\s+/ /g;
				$text =~ s/([\$\@\%])/\\$1/g;
				$text = qq($text);

				# MySQL uses indices internally to represent constraints, and so has odd syntax for the creation
				# of FOREIGN KEY constraints which allows the index which equates to the constraint to be specified
				# and, although this will generally operate equivalently to naming the constraint itself, there is
				# a semantic difference here.  At the same time, it is still valid (although unlikely to be be what
				# was intended) to specify an index name (only) and so we can only issue a warning when this occurs.
				if( $text =~ m/\sADD\s+(?:CONSTRAINT\s+)?FOREIGN\s+KEY\s*([^(][^()`,\s]+`?)[()`,\s]/i ) {
					pwarn( "index_name " . ( defined( $1 ) ? $1 : '' ) . " specified in place of CONSTRAINT symbol - this is likely a bug:\n\n$text\n", 1 );
				}

				if( ( $text =~ m/[`' (]([^`' (]+_ibfk_[0-9]+)[) '`]/ ) and not( $text =~ m/DROP\s+FOREIGN\s+KEY\s+`[^`]+_ibfk_[0-9]+`/i ) ) {
					pwarn( "Auto-generated constraint name `$1` used as deterministic CONSTRAINT symbol - this usage is deprecated:\n\n$text\n", 1 );
				}

				# Ensure that constraints are explicitly named, so that we can deterministically drop them later...
				if( ( $text =~ m/\sFOREIGN\s+KEY[\s(]/i ) and not( ( $text =~ m/\sCONSTRAINT\s+`[^`]+`\s+FOREIGN\s+KEY[\s(]/i ) or ( $text =~ m/DROP\s+FOREIGN\s+KEY\s/i ) ) ) {
					$output -> ( "Unwilling to create non-deterministic constraint from:\n\n$text\n" );
					$invalid = TRUE;
				}

				if( not( defined( $entry -> { 'tokens' } ) ) ) {
					# FIXME: Filter known edge-cases which the Parser fails to tokenise...
					if( not( $text =~ m/^((LOCK|UNLOCK|SET|CREATE\s+PROCEDURE|GRANT|TRUNCATE)\s+|\s*\/\*\!)/i ) ) {
						$output -> ( 'Unable to parse ' . $texttype . 'entry "' . $text . '"' );
						# FIXME: Don't abort simply because we hit something we can't parse...
						#$invalid = TRUE;
					}

					# FIXME: Reinstate this once the Parser has full coverage
					#$invalid = TRUE;

					next;
				}
			}

			if( defined( $entry -> { 'tokens' } -> { 'type' } ) and defined( $entry -> { 'tokens' } -> { 'object' } ) ) {
				my $type = $entry -> { 'tokens' } -> { 'type' };
				my $object = $entry -> { 'tokens' } -> { 'object' };
				if( ( defined( $type ) and ( 'create' eq lc( $type ) ) ) and ( defined( $object ) and ( 'user' eq lc( $object ) ) ) ) {
					if( defined( $tmpdir ) and -d $tmpdir ) {
						$dumpusers = TRUE unless( -e $tmpdir . '/' . 'mysql.users.sql' );
					}
				}
			}

			foreach my $key ( keys( $entry -> { 'tokens' } ) ) {
				if( ref( $entry -> { 'tokens' } -> { $key } ) eq 'ARRAY' ) {
					foreach my $element ( @{ $entry -> { 'tokens' } -> { $key } } ) {
						if( ref( $element ) eq 'HASH' ) {
							foreach my $basekey ( keys( %{ $element } ) ) {
								# N.B.: This should never occur when ( $mode eq 'procedure' )...
								if( $basekey eq 'tbl' ) {
									my $table = $element -> { $basekey };

									# FIXME:  For input 'INSERT INTO `table`(`column1`,`column2`) VALUES ...',
									#         Parser output still contains the specified attributes :(
									# Update: Actually, it's worse - the parser thinks this is a huge inner-join.
									# Update: Now fixed, hopefully...
									#$table =~ s/\([^\)]*\)//g;
									$table =~ s/`//g;

									#if( not( /^$table$/ ~~ @dumptables ) )
									if( defined( $table ) and ( not( scalar( @dumptables ) and ( qr/^$table$/ |M| \@dumptables ) ) ) ) {
										print( "=> Adding table `$table` to backup list ...\n" );
										push( @dumptables, $table );
									}
								}
							}
						}
					}
				}
			}

			$statements++;
		}
	}
	if( 0 == $statements ) {
		# Still issue a warning, but don't abort here - placeholder
		# schema should be allowed to fill gaps due to reorganisation.
		#
		warn( "!> No valid SQL statements found, but continuing for now ...\n" );
		#dbclose( undef, 'Nothing to do' );
		#return( FALSE );
	}
	if( $invalid ) {
		if( $pretend ) {
			pwarn( "SQL parsing failed - continuing with valid statements only ..." );
		} else {
			if( defined( $verbosity ) and $verbosity > 0 ) {
				die( "SQL parsing failed\n" );
			} else {
				die( "SQL parsing failed - please re-execute with the '--warn' option to display these issues\n" );
			}
		}
	}

	# }}}

	my $availabledatabases;
	my $availabletables;
	my $uuid;

	#
	# Open target database connection
	#

	print( "\n=> Connecting to database `$db` ...\n" );
	my $dsn = "DBI:mysql:database=$db;host=$host;port=$port";
	my $dbh;
	my $error = dbopen( \$dbh, $dsn, $user, $pass, $strict );
	die( $error ."\n" ) if $error;

	$uuid = getsqlvalue( $dbh, "SELECT UUID()" );

	# This shouldn't have changed before, but it does no harm to check...
	#
	$availabledatabases = getsqlvalues( $dbh, "SHOW DATABASES" );
	die( 'Unable to retrieve list of available databases' . ( defined( $dbh -> errstr() ) ? ': ' . $dbh -> errstr() : '' ) . "\n" ) unless( scalar( $availabledatabases ) );

	$availabletables = getsqlvalues( $dbh, "SHOW TABLES" );
	warn( "Unable to retrieve list of tables for database `$db`" . ( defined( $dbh -> errstr() ) ? ': ' . $dbh -> errstr() : '' ) . "\n" ) unless( scalar( $availabletables ) );

	#
	# Populate tracking tables, if necessary # {{{
	#
	# $schmversion will be the value specified on the command-line or
	# zero otherwise.
	#
	# This value is then re-calculated to match the file version (if
	# present) to avoid clashes...
	#

	my $installedrank;
	my $versionrank;

	print( "\n" ) unless( defined( $action_init ) );

	if( not( 'procedure' eq $mode ) ) {
		#if( not( /^$flywaytablename$/ ~~ @{ $availabletables } ) )
		if( defined( $flywaytablename ) and not( qr/^$flywaytablename$/ |M| \@{ $availabletables } ) ) {
			if( $pretend ) {
				warn( "!> flyway metadata table `$flywaytablename` does not exist.\n" );
			} else {
				die( "flyway metadata table `$flywaytablename` does not exist.\n" );
			}
		} else {
			#
			# Write 'init' entry, if not already present # {{{
			#

			my $init = getsqlvalue( $dbh, "SELECT COUNT(*) FROM `$flywaytablename` WHERE `success` = '1'" );
			if( defined( $init ) and ( 0 != $init ) ) {
				if( defined( $action_init ) ) {
					# FIXME: Later on, we decide that we don't trust the database to order arbitrary
					#        versions correctly, and so perform the operation manually ourselves.
					#        This should at least be made consistent...
					#
					my $version = getsqlvalue( $dbh, "SELECT `version` FROM `$flywaytablename`  WHERE `success` = '1' ORDER BY `version` DESC LIMIT 1" );
					print( "\n*> flyway metadata table `$flywaytablename` is already initialised to version '$version'.\n" );
					if( $force ) {
						if( $pretend ) {
							print( "*> Would force re-initialisation to version '$schmversion'.\n" );
						} else {
							print( "*> Forcing re-initialisation to version '$schmversion' ...\n" );
							$init = 0;
						}
					} else {
						if( $pretend ) {
							warn( "!> Database `$db` has already been initialised to version '$version' - please use '--clear-metadata' to discard.\n" );
						} else {
							die( "$fatal Database `$db` has already been initialised to version '$version' - please use '--clear-metadata' to discard.\n" );
						}
					}
				}

			} elsif( not( defined( $init ) ) or ( 0 == $init ) ) {
				$versionrank = getsqlvalue( $dbh, "SELECT MAX(`version_rank`) FROM `$flywaytablename`" );
				if( defined( $versionrank ) and $versionrank =~ m/^\d+$/ and $versionrank >= 0 ) {
					$versionrank++;
				} else {
					$versionrank = 0;
				}
				$installedrank = getsqlvalue( $dbh, "SELECT MAX(`installed_rank`) FROM `$flywaytablename`" );
				if( defined( $installedrank ) and $installedrank =~ m/^\d+$/ and $installedrank >= 0 ) {
					$installedrank++;
				} else {
					$installedrank = 0;
				}

				{
				my $replacement = getsqlvalue( $dbh, "SELECT COUNT(*) FROM `$flywaytablename` WHERE `version` = '$schmversion'" );
				my $sth;

				if( defined( $replacement ) and $replacement =~ m/^\d+$/ and 0 == $replacement ) {
					$sth = preparesql( $dbh, <<SQL );
INSERT INTO `$flywaytablename` (
    `version_rank`
  , `installed_rank`
  , `version`
  , `description`
  , `type`
  , `script`
  , `checksum`
  , `installed_by`
  , `installed_on`
  , `execution_time`
  , `success`
) VALUES ( ?, ?, ?, ?, ?, ?, ?, ?, CURRENT_TIMESTAMP, ?, ? )
SQL
					die( "Unable to create INIT statement handle: " . $dbh -> errstr() . "\n" ) unless( defined( $sth ) and $sth );
					if( $safetyoff ) {
						executesql( $dbh, $sth, undef,
							  $versionrank
							, $installedrank
							, $schmversion
							, '<< Flyway Init >>'
							, 'INIT'
							, '<< Flyway Init >>'
							,  undef
							, $user
							#  CURRENT_TIMESTAMP
							,  0
							,  1
						) or die( "Updating '$flywaytablename' with INIT failed" . ( defined( $sth -> errstr() ) ? ": " . $sth -> errstr() : ( defined( $dbh -> errstr() ) ? ": " . $dbh -> errstr() : '' ) ) . "\n" );
					}
				} else {
					# Since flyway uses `version` alone as the primary key, we have no choice but to
					# over-write and previous data of the same version if the metadata is
					# re-initialised.  The myway metadata will still store a record of previous
					# actions, however.  The explicit version is not stored, but this can be found
					# by examining the file which was loaded.
					# FIXME: There is no explicit link between a flyway entry and myway data.
					#
					$sth = preparesql( $dbh, <<SQL );
UPDATE `$flywaytablename` SET
    `version_rank` = ?
  , `installed_rank` = ?
  , `description` = ?
  , `type` = ?
  , `script` = ?
  , `checksum` = ?
  , `installed_by` = ?
  , `installed_on` = CURRENT_TIMESTAMP
  , `execution_time` = ?
  , `success` = ?
WHERE `version` = ?
SQL
					die( "Unable to create updated INIT statement handle: " . $dbh -> errstr() . "\n" ) unless( defined( $sth ) and $sth );
					if( $safetyoff ) {
						executesql( $dbh, $sth, undef,
							  $versionrank
							, $installedrank
							, '<< Flyway Init >>'
							, 'INIT'
							, '<< Flyway Init >>'
							,  undef
							, $user
							#  CURRENT_TIMESTAMP
							,  0
							,  1
							, $schmversion
						) or die( "Updating '$flywaytablename' with updated INIT failed" . ( defined( $sth -> errstr() ) ? ": " . $sth -> errstr() : ( defined( $dbh -> errstr() ) ? ": " . $dbh -> errstr() : '' ) ) . "\n" );
					}
				}
				$sth -> finish();
				}
				if( not( $pretend ) ) {
					print( "\n*> flyway metadata table `$flywaytablename` has been initialised to version '$schmversion':\n" );
					formatastable( $dbh, "SELECT * FROM $flywaytablename ORDER BY `version` DESC LIMIT 5", '   ' );
				}
			}
			if( not( defined( $file ) ) or defined( $action_init ) ) {
				dbclose( $dbh );
				return( TRUE );
			}

			# }}}

			# We need to perform a version-sort here, because we
			# need to skip all files /less than or/ equal to the
			# initialiser...
			#
			# FIXME: We only consider file-version here, rather
			#        rather than meta-data versions.  We later
			#        issue a warning if these two versions differ.
			#
			# Cases: {0, 0.3}; {0.1, 0.3}; {0.3, 0.3}; {0.3, 0.5}.
			#            ^^^         ^^^         ^^^    ^^^
			#
			my $version = getsqlvalue( $dbh, "SELECT `version` FROM `$flywaytablename`  WHERE `success` = '1' AND `type` = 'INIT' ORDER BY `version` DESC LIMIT 1" );
			if( not( defined( $version ) and length( $version ) ) ) {
				if( not( $force ) ) {
					die( "Database has not been initialised with this tool - please re-run with '--init' and the appropriate schema-file version number.\n" );
				} else {
					warn( "!> Database has not been initialised with this tool - will force-apply file '$schmfile' ...\n" );
				}
			} else {
				if( $schmfile =~ m/^V(.*?)__/ ) {
					my $match = $1;
					my @sortedversions = sort { versioncmp( $a, $b ) } ( $version, $match );
					my $latest = pop( @sortedversions );
					my $previous = pop( @sortedversions );
					if( not( $force ) ) {
						if( ( $match eq $latest ) and ( $latest eq $previous ) ) {
							print( "=> Skipping base initialiser file '$schmfile' ...\n" );
							dbclose( $dbh );
							return( TRUE );
						} elsif( $match eq $previous ) {
							print( "=> Skipping pre-initialisation file '$schmfile' ...\n" );
							dbclose( $dbh );
							return( TRUE );
						}
					}
				}
			}

			$schmversion = $action_init;
			$schmversion = $1 if( not( defined( $schmversion ) and length( $schmversion ) ) and ( $schmfile =~ m/^V(.*?)__/ ) );
			$schmversion = '0' unless( defined( $schmversion ) and length( $schmversion ) );
			my $metadataversions = getsqlvalues( $dbh, "SELECT DISTINCT(`version`) FROM `$flywaytablename` WHERE `success` = '1'" );
			#if( /^$schmversion$/ ~~ $metadataversions )
			if( defined( $schmversion ) and ( qr/^$schmversion$/ |M| $metadataversions ) ) {
				if( $pretend ) {
					if( $force ) {
						warn( "!> Schema version '$schmversion' has already been applied to this database - would forcibly re-apply ...\n" );
					} else {
						warn( "!> Schema version '$schmversion' has already been applied to this database - would skip ...\n" );
					}
				} else {
					if( $force ) {
						warn( "!> Schema version '$schmversion' has already been applied to this database - forcibly re-applying ...\n" );
					} else {
						warn( "!> Schema version '$schmversion' has already been applied to this database - skipping ...\n\n" );
						return( TRUE );
					}
				}
			}

			$versionrank = getsqlvalue( $dbh, "SELECT MAX(`version_rank`) FROM `$flywaytablename`" );
			if( defined( $versionrank ) and $versionrank =~ m/^\d+$/ and $versionrank >= 0 ) {
				$versionrank++;
			} else {
				$versionrank = 0;
			}
			$installedrank = getsqlvalue( $dbh, "SELECT MAX(`installed_rank`) FROM `$flywaytablename`" );
			if( defined( $installedrank ) and $installedrank =~ m/^\d+$/ and $installedrank >= 0 ) {
				$installedrank++;
			} else {
				$installedrank = 0;
			}

			{
			my $sth = preparesql( $dbh, <<SQL );
INSERT INTO `$mywaytablename` (
    `id`
  , `dbuser`
  , `dbhost`
  , `osuser`
  , `host`
  , `sha1sum`
  , `path`
  , `filename`
  , `started`
) VALUES ( ?, ?, ?, ?, ?, ?, ?, ?, SYSDATE() )
SQL
# Unchanged: `sqlstarted`, `finished`, `status`.
			die( "Unable to create tracking statement handle: " . $dbh -> errstr() . "\n" ) unless( defined( $sth ) and $sth );
			my $uid = ( $ENV{ LOGNAME } or $ENV{ USER } or getpwuid( $< ) );
			my $oshost = qx( hostname -f );
			my $sum = qx( sha1sum \"$file\" );
			chomp( $oshost );
			chomp( $sum );
			$sum =~ s/\s+.*$//;
			if( $safetyoff ) {
				executesql( $dbh, $sth, undef,
					   $uuid
					,  $user
					,  $host
					,  $uid
					,  $oshost
					,  $sum
					,  $schmpath
					,  $schmfile

				);
			}
			$sth -> finish();
			}
		}
	}
	#else { # ( 'procedure' eq $mode )
	#	# This case is handled below, during file metadata-parsing...
	#}

	# }}}

	#
	# Perform backups # {{{
	#

	# TODO: Backup Stored Procedures also?
	if( $statements and not( ( 'procedure' eq $mode ) or $unsafe ) ) {
		if( $dumpusers ) {

			# I can't imagine that this will change any time soon,
			# but I guess it's not impossible that at some future
			# time `maria` is the system database... ?
			my $systemdb = 'mysql';

			if( $pretend ) {
				print( "\nS> User alterations detected - would back-up MySQL `users` tables.\n" );
			} else {
				#if( not( /^mysql$/ ~~ @{ $availabledatabases } ) )
				if( not( qr/^$systemdb$/ |M| \@{ $availabledatabases } ) ) {
					warn( "`$systemdb` database does not appear to exist.  Detected databases were:\n" );
					foreach my $database ( @{ $availabledatabases } ) {
						warn( "\t$database\n" );
					}
					die( "Aborting\n" );
				}

				#
				# Populate list of system tables, for user-backup purposes
				#

				my $availablesystemtables;

				print( "\n=> Connecting to database `$systemdb` ...\n" );
				my $systemdsn = "DBI:mysql:database=$systemdb;host=$host;port=$port";
				my $systemdbh;
				my $systemerror = dbopen( \$systemdbh, $systemdsn, $user, $pass, $strict );
				die( $systemerror ."\n" ) if $systemerror;

				$availablesystemtables = getsqlvalues( $systemdbh, "SHOW TABLES" );
				warn( "Unable to retrieve list of tables for database `$systemdb`" . ( defined( $systemdbh -> errstr() ) ? ': ' . $systemdbh -> errstr() : '' ) . "\n" ) unless( scalar( $availablesystemtables ) );

				dbclose( $systemdbh );

				my @usertables = ( 'columns_priv', 'procs_priv', 'proxies_priv', 'tables_priv', 'user' );
				my @backuptables;
				my $showtables = FALSE;
				foreach my $table ( @usertables ) {
					#if( not( /^$table$/ ~~ @{ $availablesystemtables } ) )
					if( qr/^$table$/ |M| \@{ $availablesystemtables } ) {
						push( @backuptables, $table );
					} else {
						warn( "`$table` table does not appear to exist in `$systemdb` database.\n" );
						$showtables = TRUE;
					}
				}
				if( $showtables ) {
					warn( "Detected databases were:\n" );
					foreach my $table ( @{ $availabletables } ) {
						warn( "\t$table\n" );
					}
					die( "Aborting\n" ) if( not( @backuptables ) or ( 0 == scalar( @backuptables ) ) );
				}

				print( "\n=> User alterations detected - backing-up MySQL `user` and *`_priv` tables ...\n" );

				my $auth = {
					  'user'	=> $user
					, 'password'	=> $pass
					, 'host'	=> $host
					, 'database'	=> $systemdb
				};
				dbdump( $auth, \@backuptables, $tmpdir, "mysql.userpriv.$uuid.sql" ) or die( "Database backup failed - aborting\n" );

				print( "\n=> MySQL table backups completed\n" );
			}
		}
		if( scalar( @dumptables ) ) {

			# We could backup everything at once, but it's likely
			# more helpful to have individual files per table...
			#
			foreach my $table ( @dumptables ) {
				#if( not( /^$table$/ ~~ @{ $availabletables } ) )
				if( defined( $table ) and not( qr/^$table$/ |M| \@{ $availabletables } ) ) {
					print( "=> Referenced table `$table` has not yet been created ...\n" );
				} else {
					if( $pretend ) {
						print( "\nS> Would back-up table `$table`.\n" );
					} else {
						print( "\n=> Backing-up table `$table`...\n" );

						my $auth = {
							  'user'	=> $user
							, 'password'	=> $pass
							, 'host'	=> $host
							, 'database'	=> $db
						};
						dbdump( $auth, $table, $tmpdir, "$db.$table.$uuid.sql" ) or die( "Database backup failed - aborting\n" );

						print( "\n=> Backup of  `$db`.`$table` completed with UUID '$uuid'\n" );
					}
				}
			}
		}
		# Populate regardless...
		#
		#if( $dumpusers or( scalar( @dumptables ) ) ) {
			if( $pretend ) {
				print( "S> Would update myway timing metadata for invocation '$uuid' due to " . ( ( $dumpusers or( scalar( @dumptables ) ) ) ? "backups completed" : "SQL execution starting" ) . " ...\n" );
			} else {
				dosql( $dbh, "START TRANSACTION" ) or die( "Failed to start transaction\n" );
				print( "=> Updating myway timing metadata for invocation '$uuid' due to " . ( ( $dumpusers or( scalar( @dumptables ) ) ) ? "backups completed" : "SQL execution starting" ) . " ...\n" );
				my $sql = "UPDATE `$mywaytablename` SET `sqlstarted` = SYSDATE() WHERE `id` = '$uuid'";
				dosql( $dbh, $sql ) or die( "Closing statement execution failed\n" );

				if( 'procedure' eq $mode ) {
					print( "=> Committing transaction data\n" );
					dosql( $dbh, "COMMIT" ) or die( "Failed to commit transaction\n" );
				}
			}
		#}
	}

	# }}}

	my $laststatementwasddl = undef;
	my $firstcomment = TRUE;
	my $secondcomment = undef;
	my $schmdescription = undef;
	my $schmprevious = undef;
	my $schmtarget = undef;

	if( 'procedure' eq $mode ) {
		# N.B. This logic does mean that any valid SQL statements in
		#      a given metadata file will be executed for /every/
		#      stored procedure within a given directory... the
		#      intention is that metadata should contain comments only
		#      (see warning above).
		my @entries;
		foreach my $entry ( $metadata -> { 'entries' } ) {
			push( @entries, @{ $entry } );
		}
		foreach my $entry ( $data -> { 'entries' } ) {
			push( @entries, @{ $entry } );
		}
		$data -> { 'entries' } = \@entries;
	}

	my $schemastart = [ gettimeofday() ];

	my $delim = DEFDELIM;
	foreach my $entry ( $data -> { 'entries' } ) {
		foreach my $statement ( @{ $entry } ) {
			if( 'comment' eq $statement -> { 'type' } ) {
				if( 'ARRAY' eq ref( $statement -> { 'entry' } ) ) { # {{{
					#
					# Version-tracking data must be in an
					# array in the first comment - we don't
					# process data in following comments,
					# or any non-standard format with
					# multiple tracking items on different
					# lines.
					#
					# FIXME: We'll only consider single-
					#        line Description fields, too.
					#
					if( defined( $firstcomment ) or ( ( 'procedure' eq $mode ) and defined( $secondcomment ) ) ) { # {{{
						foreach my $line ( @{ $statement -> { 'entry' } } ) {
							chomp( $line );
							if( $line =~ m/Description:\s+(.*)\s*$/i ) {
								$schmdescription = $1;
							}
							if( $line =~ m/Previous\s+version:\s+([^\s]+)\s*/i ) {
								$schmprevious = $1;
							}
							if( $line =~ m/Target\s+version:\s+([^\s]+)\s*/i ) {
								$schmtarget = $1;
							}
						}
						$schmprevious = undef if( defined( $schmprevious ) and ( $schmprevious =~ m#(?:na|n/a)#i ) );
						print( "*> Read dubious prior version '$schmprevious'\n" ) unless( not( defined( $schmprevious ) ) or ( $schmprevious =~ m/[\d.]+/ ) );
						print( "*> Read dubious target version '$schmtarget'\n" ) unless( not( defined( $schmtarget ) ) or ( $schmtarget =~ m/[\d.]+/ ) );
						if( ( $schmfile =~ m/^(?:V(?:.*?)__)*V(.*?)__/ ) and not( $1 =~ m/^$schmtarget(?:\.\d+)?$/ ) ) {
							warn( "!> $warning File-name version '$1' differs from metadata version '$schmtarget' from file '$schmfile'\n" );
						}

						if( defined( $firstcomment ) ) {
							my $oldstatus = $status;
							my $greaterversionpresent = FALSE;

							my $tablename = $flywaytablename;
							my $statuscolumn = 'success';
							$status = "TRUE";
							if( 'procedure' eq $mode ) {
								$tablename = $mywayprocsname;
								$statuscolumn = 'status';
								$status = "'$status'";
							}

							if( not( defined( $schmtarget ) and length( $schmtarget ) ) ) {
								if( not( 'procedure' eq $mode ) ) {
									warn( "!> No target version defined in schema comments - relying on filename alone\n" );
								} else {
									warn( "!> No target version defined in metadata comments - not validating target installation chain\n" );
								}

							#} elsif( not( /^$flywaytablename$/ ~~ @{ $availabletables } ) )
							} elsif( defined( $tablename ) and not( qr/^$tablename$/ |M| \@{ $availabletables } ) ) {
								warn( "!> metadata table `$tablename` does not exist - not validating target installation chain\n" );

							} else {
								# N.B. Logic change - previously, we were simply checking that the target version
								#      hasn't been applied to the database.  Now, we're checking that nothing
								#      newer than the target has been applied either.

								# We could sort in the database here, but I'm not sure "ORDER BY" would cope with the
								# various versions we might be trying to throw at it...
								#
								my $installedversions = getsqlvalues( $dbh, "SELECT DISTINCT(`version`) FROM `$tablename` WHERE `$statuscolumn` = $status" );
								die( 'Unable to retrieve list of installed schema versions' . ( defined( $dbh -> errstr() ) ? ': ' . $dbh -> errstr() : '' ) . "\n" ) unless( scalar( $installedversions ) );

								my $okay = TRUE;
								my $fresh = TRUE;

								#if( /^$schmtarget$/ ~~ $installedversions )
								if( qr/^$schmtarget$/ |M| $installedversions ) {
									if( not( $first ) and ( 'procedure' eq $mode ) ) {
										# Duplicate installs are the norm for Stored Procedure installations, as each
										# definition is applied with the same metadata version.
										#
										$fresh = FALSE;
									} else {
										if( $pretend ) {
											if( $force or ( 'procedure' eq $mode ) ) {
												warn( "!> " . ( ( 'procedure' eq $mode ) ? 'Stored Procedure' : 'Schema' ) . " target version '$schmtarget' has already been applied to this database - would forcibly re-apply ...\n" );
											} else {
												warn( "!> " . ( ( 'procedure' eq $mode ) ? 'Stored Procedure' : 'Schema' ) . " target version '$schmtarget' has already been applied to this database - would skip ...\n" );
											}
										} else {
											if( $force or ( 'procedure' eq $mode ) ) {
												warn( "!> " . ( ( 'procedure' eq $mode ) ? 'Stored Procedure' : 'Schema' ) . " target version '$schmtarget' has already been applied to this database - forcibly applying ...\n" );
											} else {
												warn( "!> Schema target version '$schmtarget' has already been applied to this database - skipping ...\n" );
												return( TRUE );
											}
										}
										$okay = FALSE;
										$fresh = FALSE;
									}
								}

								my( $codeversion, $changeversion, $stepversion, $hotfixversion ) = ( $schmfile =~ m/^V([[:xdigit:]]+)\.([0-9]+)\.([0-9]+)\.([0-9]+)__/ );

								my @sortedversions = sort { versioncmp( $a, $b ) } ( @{ $installedversions }, $schmtarget );
								my $latest = pop( @sortedversions );
								if( not( $latest eq $schmtarget ) ) {
									if( not( 'procedure' eq $mode ) and defined( $hotfixversion ) and not( $hotfixversion =~ m/0+/ ) ) {
										if( $pretend ) {
											warn( "!> Hot-fix Schema version '$schmtarget' would be applied onto existing Schema version '$latest' ...\n" );
										} else {
											warn( "!> Hot-fix Schema version '$schmtarget' will be applied onto existing Schema version '$latest' ...\n" );
										}
										print( "*> Schema version '$schmtarget' is a fresh install\n" );
										$okay = TRUE;
									} else {
										if( $pretend ) {
											if( $force ) {
												warn( "!> Existing " . ( ( 'procedure' eq $mode ) ? 'Stored Procedure' : 'Schema' ) . " version '$latest' is greater than target '$schmtarget', and has already been applied to this database - would forcibly re-apply ...\n" );
											} else {
												warn( "!> Existing " . ( ( 'procedure' eq $mode ) ? 'Stored Procedure' : 'Schema' ) . " version '$latest' is greater than target '$schmtarget', and has already been applied to this database - would skip ...\n" );
											}
										} else {
											if( $force ) {
												warn( "!> Existing " . ( ( 'procedure' eq $mode ) ? 'Stored Procedure' : 'Schema' ) . " version '$latest' is greater than target '$schmtarget', and has already been applied to this database - forcibly applying ...\n" );
											} else {
												warn( "!> Existing " . ( ( 'procedure' eq $mode ) ? 'Stored Procedure' : 'Schema' ) . " version '$latest' is greater than target '$schmtarget', and has already been applied to this database - skipping ...\n" );
												return( TRUE );
											}
										}
										$greaterversionpresent = TRUE;
										$okay = FALSE;
									}
								} elsif( $fresh ) { # and ( $first )
									print( "*> " . ( ( 'procedure' eq $mode ) ? 'Stored Procedure' : 'Schema' ) . " version '$schmtarget' is a fresh install\n" );
								} elsif( $first ) {
									print( "*> " . ( ( 'procedure' eq $mode ) ? 'Stored Procedure' : 'Schema' ) . " version '$schmtarget' is a re-install\n" );
								}
								if( $okay ) {
									$schmversion = $schmtarget;
								}
							}

							if( not( defined( $schmprevious ) ) ) {
								print( "*> No previous version defined in schema comments - not validating previous installation chain\n" );
							#} elsif( not( /^$flywaytablename$/ ~~ @{ $availabletables } ) )
							} elsif( defined( $tablename ) and not( qr/^$tablename$/ |M| \@{ $availabletables } ) ) {
								warn( "!> metadata table `$tablename` does not exist - not validating previous installation chain\n" );
							} else {
								# Ensure that we only consider successfully-applied versions (via $status)...
								#
								# N.B.: $status is pre-quoted
								#
								my $installedversions = getsqlvalues( $dbh, "SELECT DISTINCT(`version`) FROM `$tablename` WHERE `$statuscolumn` = $status" );
								push( @{ $installedversions }, $schmvirtual ) if( defined( $schmvirtual ) );
								die( 'Unable to retrieve list of installed schema versions' . ( defined( $dbh -> errstr() ) ? ': ' . $dbh -> errstr() : '' ) . "\n" ) unless( scalar( $installedversions ) );

								#if( $schmprevious =~ m/^0(?:\.0+)?$/ ) {
									#$schmprevious = '0(?:\.0+)?';
								#}
								my $schmpreviousmatch = $schmprevious;
								my $regex = qr/0(?:(?:\.0+)+)?/;
								if( $schmprevious =~ m/^$regex$/ ) {
									$schmpreviousmatch = "$regex";
								}
								if( $greaterversionpresent ) {
									print( "*> Not validating previous versions as target version has already been exceeded\n" );
								} else {
									#if( /^$schmprevious$/ ~~ $installedversions )
									if( defined( $schmpreviousmatch ) and ( qr/^$schmpreviousmatch(?:\.\d)?$/ |M| $installedversions ) ) {
										if( 'procedure' eq $mode ) {
											pdebug( "Prior Stored Procedure definitions '$schmprevious' exist in myway metadata" );
										} else {
											pdebug( "Prior schema version '$schmprevious' correctly exists in flyway metadata" );
										}
									} else {
										if( 'procedure' eq $mode ) {
											# Stored Procedures should be entirely self-contained, so we can apply any
											# future version at any point, regardless of what is already present (with
											# and cleanup/migration performed by metadata commands).  Therefore, lacking
											# a previous version is not an issue, but we shouldn't allow installation of
											# older and duplicate definitions without '--force'.
											#
											print( "*> Prior Stored Procedure definitions '$schmprevious' have not been applied to this database\n" );
										} else {
											if( $pretend ) {
												if( $force ) {
													warn( "!> Prior schema version '$schmprevious' has not been applied to this database - would forcibly apply ...\n" );
												} else {
													warn( "!> Prior schema version '$schmprevious' has not been applied to this database - would abort.\n" );
												}
											} else {
												if( $force ) {
													warn( "!> Prior schema version '$schmprevious' has not been applied to this database - forcibly applying ...\n" );
												} else {
													die( "Prior schema version '$schmprevious' (required by '$schmfile') has not been applied to this database - aborting.\n" );
												}
											}
										}
									}
								}
							}

							if( not( $statements ) and not( defined( $schmprevious ) and defined( $schmtarget ) ) ) {
								warn( "!> No valid SQL statements found; previous and target versions are not both defined\n" );
								dbclose( undef, 'Nothing to do' );
								return( TRUE );
							}

							$status = $oldstatus;

							# We finally know that Stored Procedures are safe to apply!
							if( 'procedure' eq $mode ) {
								if( defined( $mywayprocsname ) and not( qr/^$mywayprocsname$/ |M| \@{ $availabletables } ) ) {
									# We've already said this by this point...
									#warn( "!> metadata table `$mywayprocsname` does not exist - not validating target installation chain\n" );
								} else {
									# This is wrong - as we're processing separate files, we do need to store
									# metadata entries for every file...
									#

									#my $metadataversions = getsqlvalues( $dbh, "SELECT DISTINCT(`version`) FROM `$mywayprocsname` WHERE `status` = '$status'" );
									##if( /^$schmversion$/ ~~ $metadataversions )
									#if( not( $first ) and ( qr/^$schmversion$/ |M| $metadataversions ) ) {
									#	pdebug( "Metadata for version '$schmversion' already exists ..." );
									#} else {
									#	# Only write metadata once per invocation, for first file only...
									#	#

									# For this to work, we /have/ to assume that filenames are consistent and
									# that they are always named '<function_name>.sql'...
									#
									my $metadataversions = getsqlvalues( $dbh, "SELECT DISTINCT(`version`) FROM `$mywayprocsname` WHERE `filename` = '$schmfile' AND `status` = '$status'" );
									if( qr/^$schmversion$/ |M| $metadataversions ) {
										pdebug( "Metadata for file '$schmfile' version '$schmversion' already exists ..." );
									} else {

										my $uid = ( $ENV{ LOGNAME } or $ENV{ USER } or getpwuid( $< ) );
										my $oshost = qx( hostname -f );
										my $sum = qx( sha1sum \"$file\" );
										chomp( $oshost );
										chomp( $sum );
										$sum =~ s/\s+.*$//;

										my $sth = preparesql( $dbh, <<SQL );
INSERT INTO `$mywayprocsname` (
    `id`
  , `dbuser`
  , `dbhost`
  , `osuser`
  , `host`
  , `sha1sum`
  , `path`
  , `filename`
  , `started`
) VALUES ( ?, ?, ?, ?, ?, ?, ?, ?, SYSDATE() )
SQL
# Currently unchanged values: `version`, `description`, `type`, `sqlstarted`, `finished`, `status`.
										die( "Unable to create tracking statement handle: " . $dbh -> errstr() . "\n" ) unless( defined( $sth ) and $sth );
										if( $safetyoff ) {
#warn "DEBUG: Inserting entry to `$mywayprocsname` for file '$schmfile'";
											pdebug( "DEBUG: Inserting entry to `$mywayprocsname` for file '$schmfile'" );
											executesql( $dbh, $sth, undef,
												   $uuid
												,  $user
												,  $host
												,  $uid
												,  $oshost
												,  $sum
												,  $schmpath
												,  $schmfile

											);
										}
										$sth -> finish();
									}
								}
							} # ( 'procedure' eq $mode )
						} # defined( $firstcomment )

						if( defined( $firstcomment ) or ( ( 'procedure' eq $mode ) and defined( $secondcomment ) ) ) {
							if( defined( $firstcomment ) ) {
								$firstcomment = undef;
								$secondcomment = TRUE;
							} else {
								$secondcomment = undef;
							}
						}

						if( defined( $schmdescription ) and length( $schmdescription ) ) {
							if( defined( $desc ) ) {
								print( "*> Updating schema description from '$desc' to '$schmdescription'\n" );
							} else {
								print( "*> Updating schema description to '$schmdescription'\n" );
							}
							$desc = $schmdescription;
						}

						print( "\n" ) if( $verbosity );
					} # }}}
					foreach my $line ( @{ $statement -> { 'entry' } } ) {
						chomp( $line );
						# Hints are no longer passed as comments, so this block
						# is no longer necessary...
						#if( $line =~ m:/\*![0-9]{5} (.+) \*/: ) {
						#	print( "-> Hint: " . $1 . "\n" ) if( $verbosity );
						#	if( $safetyoff ) {
						#		dosql( $dbh, $line ) or die( "Statement execution failed\n" );
						#	}
						#} else {
							print( " > " . $line . "\n" ) if( $verbosity );
						#}
					}
				} else {
					my $line = $statement -> { 'entry' };
					chomp( $line );
					# Hints are no longer passed as comments, so this block
					# is no longer necessary...
					#if( $line =~ m:/\*![0-9]{5} (.+) \*/: ) {
					#	print( "-> Hint: " . $1 . "\n" ) if( $verbosity );
					#	if( $safetyoff ) {
					#		dosql( $dbh, $line ) or die( "Statement execution failed\n" );
					#	}
					#} else {
						print( " > " . $line . "\n" ) if( $verbosity );
					#}
				} # }}}
			} elsif( 'statement' eq $statement -> { 'type' } ) {
				if( defined( $statement -> { 'tokens' } -> { 'type' } ) and ( $statement -> { 'tokens' } -> { 'type' } ) ) { # {{{
					my $type = $statement -> { 'tokens' } -> { 'type' };
					if( $type =~ m/delete|delimiter|grant|insert|replace|select|update/i ) {
						if( $type =~ m/delimiter/i ) {
							$delim = $statement -> { 'tokens' } -> { 'delimiter' } if( defined( $statement -> { 'tokens' } -> { 'delimiter' } ) and length( defined( $statement -> { 'tokens' } -> { 'delimiter' } ) ) );
						}

						if( defined( $laststatementwasddl ) and not( $laststatementwasddl ) ) {
							# Last statement was not DDL, so we can still
							# roll-back.

						} elsif( not( 'procedure' eq $mode ) ) { # not( defined( $laststatementwasddl ) ) or $laststatementwasddl
							# Last statement was DDL, (or this is our
							# first statement) so start a new
							# transaction...

							if( $pretend ) {
								print( "S> Would commence new transaction\n" );
							} else {
								print( "=> Commencing new transaction\n" );
								dosql( $dbh, "START TRANSACTION" ) or die( "Failed to start transaction\n" );
							}
							$laststatementwasddl = FALSE;
						}
					} elsif( $type =~ m/call|alter|create|drop/i ) {
						if( defined( $laststatementwasddl ) ) {
							if( $laststatementwasddl ) {
								# Last statement was also DDL, so we
								# can't make use of transactions.

							} elsif( not( 'procedure' eq $mode ) ) { # not( $laststatementwasddl )
								# Last statement wasn't DDL, so end
								# that transaction...

								if( $pretend ) {
									print( "S> Would commit transaction data\n" );
								} else {
									print( "=> Committing transaction data\n" );
									dosql( $dbh, "COMMIT" ) or die( "Failed to commit transaction\n" );
								}
								$laststatementwasddl = TRUE
							}
						} else { # not( defined( $laststatementwasddl ) )
							# First statement is DDL, so no need to start
							# a transaction.

							$laststatementwasddl = TRUE;
						}

					#print Dumper $statement if( $type =~ m/create/i );

					#} elsif( $type =~ m/call|delimiter/i ) {
						# The first of these could do anything, the latter
						# nothing....

					} else {
						warn( "Unknown DDL/non-DDL statement type '$type'\n" );
					}
				}

				my $sql;
				foreach my $line ( @{ $statement -> { 'entry' } } ) {
					chomp( $line );
					$line =~ s/^\s+//;
					$line =~ s/\s+$//;
					if( $verbosity ) {
						if( $line =~ m:^(.*)/\*![0-9]{5} (.+) \*/;?(.*)$: ) {
							my $statement = '';
							$statement .= $1 if( defined( $1 ) and length( $1 ) );
							$statement .= $3 if( defined( $3 ) and length( $3 ) );
							print( "-> Hint: " . $2 . "\n" );
							print( "-> " . $statement . "\n" ) if( length( $statement ) );
						} else {
							print( "-> " . $line . "\n" );
						}
					}

					# FIXME: Hack!!
					$line =~ s/\$\$\s*$//;

					# 'DELIMITER' isn't a reserved-word,
					# but /really/ should be!
					#if( not( $line =~ m/^\s*DELIMITER\s/i ) ) {
					if( not( $line =~ m/(?:^\s*|$delim\s+)DELIMITER\s/i ) ) {
						$sql .= ' ' . $line;
					}
				}
				if( defined( $sql ) ) {
					$sql =~ s/^\s+//; $sql =~ s/\s+$//;
				}

				if( defined( $sql ) and length( $sql ) ) {
					#eval {
					#	my $result = $dbh -> do( $sql );
					#};
					#if( $@ or ( not( defined( $result ) ) ) ) {
					#	die( "Error when processing SQL statement:\n$sql\n" );
					#}

					my( $started, $start, $elapsed );
					if( $safetyoff ) {
						my $realsql = $sql;

						if( $realsql =~ m/^\s*LOCK\s+TABLES/ ) {
							$realsql =~ s/;\s*$//;
							$realsql .= ", $mywayactionsname WRITE";
						}

						# This is a bit of a hack...
						$started = getsqlvalue( $dbh, "SELECT SYSDATE()" );

						$start = [ gettimeofday() ];
						dosql( $dbh, $realsql ) or die( "Statement execution failed\n" );
						$elapsed = tv_interval( $start, [ gettimeofday() ] );
					}

					if( not( 'procedure' eq $mode ) ) {
						my $sth = preparesql( $dbh, <<SQL );
INSERT INTO `$mywayactionsname` (
    `schema_id`
  , `started`
  , `event`
  , `statement`
  , `line`
  , `time`
  , `state`
) VALUES ( ?, ?, ?, ?, ?, ?, ? )
SQL
						my $error = $dbh -> errstr();
						die( "Unable to create tracking statement handle" . ( defined( $error ) and length( $error ) ? ": " . $error . "\n" : '' ) ) unless( defined( $sth ) and $sth );
						if( $safetyoff ) {
							executesql( $dbh, $sth, undef,
								   $uuid
								,  $started
								, 'execute'
								,  $sql
								,  $statement -> { 'line' }
								,  $elapsed
								,  $sth -> state()
							);
						}
						$sth -> finish();
					} else { # ( 'procedure' eq $mode )
						if( $safetyoff ) {
							my $started = getsqlvalue( $dbh, "SELECT `sqlstarted` FROM `$mywayprocsname` WHERE `id` = '$uuid'" );
							if( not( defined( $started ) ) or ( 'NULL' eq $started ) ) {
								print( "=> Updating myway timing metadata for stored procedure invocation '$uuid' due to creation commencing ...\n" );
								my $sql = "UPDATE `$mywayprocsname` SET `sqlstarted` = SYSDATE() WHERE `id` = '$uuid'";
								dosql( $dbh, $sql ) or die( "Statement execution failed\n" );
							}
						}
					}
				} # }}}
			} else {
				die( "Unknown statement type '" . $statement -> { 'type' } . "'\n" );
			}
			print( "\n" ) if( $verbosity );
		} # foreach my $statement ( @{ $entry } )

		if( not( 'procedure' eq $mode ) ) {
			if( $pretend ) {
				print( "S> Would commit transaction data\n" );
			} else {
				print( "=> Committing transaction data\n" );
				dosql( $dbh, "COMMIT" ) or die( "Failed to commit transaction\n" );
			}
		}
	} # foreach my $entry ( $data -> { 'entries' } )

	my $schemaelapsed = tv_interval( $schemastart, [ gettimeofday() ] );

	my $tablename = $mywaytablename;
	$tablename = $mywayprocsname if( 'procedure' eq $mode );

	if( $pretend ) {
		print( "S> Would update myway metadata for invocation '$uuid' ...\n" );
	} else {
		my $oldstatus = $status;
		$status = 1 if( not( 'procedure' eq $mode ) );

		dosql( $dbh, "START TRANSACTION" ) or die( "Failed to start transaction\n" );
		print( "=> Updating myway metadata for invocation '$uuid' ...\n" );
		my $sql = "UPDATE `$tablename` SET `status` = '$status', `finished` = SYSDATE() WHERE `id` = '$uuid'";
		dosql( $dbh, $sql ) or die( "Closing statement execution failed\n" );

		$status = $oldstatus;
	}

	#if( not( /^$flywaytablename$/ ~~ @{ $availabletables } ) )
	if( defined( $tablename ) and not( qr/^$tablename$/ |M| \@{ $availabletables } ) ) {
		print( "*> Would update " . ( 'procedure' eq $mode ? '' : 'flyway ' ) . "metadata with version '$schmversion', if it existed ...\n" );
	} else {
		if( $pretend ) {
			print( "S> Would update " . ( 'procedure' eq $mode ? '' : 'flyway ' ) . "metadata with version '$schmversion' ...\n" );
		} else {
			print( "=> Updating " . ( 'procedure' eq $mode ? '' : 'flyway ' ) . "metadata with version '$schmversion' ...\n" );
		}
		if( not( 'procedure' eq $mode ) ) {
			{
			my $replacement = getsqlvalue( $dbh, "SELECT COUNT(*) FROM `$flywaytablename` WHERE `version` = '$schmversion'" );
			my $sth;

			if( defined( $replacement ) and $replacement =~ m/^\d+$/ and 0 == $replacement ) {
				$sth = preparesql( $dbh, <<SQL );
INSERT INTO `$flywaytablename` (
    `version_rank`
  , `installed_rank`
  , `version`
  , `description`
  , `type`
  , `script`
  , `checksum`
  , `installed_by`
  , `installed_on`
  , `execution_time`
  , `success`
) VALUES ( ?, ?, ?, ?, ?, ?, ?, ?, CURRENT_TIMESTAMP, ?, ? )
SQL
				die( "Unable to create tracking statement handle: " . $dbh -> errstr() . "\n" ) unless( defined( $sth ) and $sth );
				if( $safetyoff ) {
					dosql( $dbh, "UNLOCK TABLES" );
					executesql( $dbh, $sth, undef,
						  $versionrank
						, $installedrank
						, $schmversion
						, $desc
						, $filetype
						, $schmfile
						   # flyway appears to initialise the checksum value at
						   # version_rank, then for each element of the table
						   # multiplies this by 31 and adds the hashCode() value
						   # associated with the item in question (or zero if null),
						   # except for 'execution_time' and 'success', which are
						   # added directly.  This (large) value is then written to a
						   # signed int(11) attribute in the database, which causes
						   # the value to wrap.
						   # I'm not going to try to reproduce this scheme here...
						,  0
						, $user
						,  int( $schemaelapsed + 0.5 )
						,  1
					);
				}
			} else {
				# Again, since `version` alone is the primary key, the `success` field is fairly
				# useless :(
				#
				$sth = preparesql( $dbh, <<SQL );
UPDATE `$flywaytablename` SET
    `version_rank` = ?
  , `installed_rank` = ?
  , `description` = ?
  , `type` = ?
  , `script` = ?
  , `checksum` = ?
  , `installed_by` = ?
  , `installed_on` = CURRENT_TIMESTAMP
  , `execution_time` = ?
  , `success` = ?
WHERE `version` = ?
SQL
				die( "Unable to create updated tracking statement handle: " . $dbh -> errstr() . "\n" ) unless( defined( $sth ) and $sth );
				if( $safetyoff ) {
					dosql( $dbh, "UNLOCK TABLES" );
					executesql( $dbh, $sth, undef,
						  $versionrank
						, $installedrank
						, $desc
						, $filetype
						, $schmfile
						,  0
						, $user
						,  int( $schemaelapsed + 0.5 )
						,  1
						, $schmversion
					);
				}
			}
			$sth -> finish();
			}
		} else {
			my $sth = preparesql( $dbh, <<SQL );
UPDATE `$mywayprocsname` SET
    `version` = ?
  , `description` = ?
  , `type` = ?
WHERE `id` = ?
SQL
# `finished` and `status` were UPDATEd just prior...
			die( "Unable to create tracking statement handle: " . $dbh -> errstr() . "\n" ) unless( defined( $sth ) and $sth );
			if( $safetyoff ) {
				dosql( $dbh, "UNLOCK TABLES" );
				executesql( $dbh, $sth, undef,
					  $schmversion
					, $desc
					, $filetype
					, $uuid
				);
			}
			$sth -> finish();
		}
	}

	if( $safetyoff ) {
		dosql( $dbh, "COMMIT" ) or die( "Failed to commit transaction\n" );
	}
	dbclose( $dbh );

	return( \$schmversion );
} # applyschema # }}}

sub main( @ ) { # {{{
	my( @argv ) = @_;

	my $port = PORT;
	my $marker = MARKER;

	#
	# Populate command-line arguments # {{{
	#

	my( $action_backup, $action_restore, $action_init );
	my( $action_migrate, $action_check );
	my( $mode, $dosub );
	my( $help, $desc, @paths, $file, $unsafe, $keepbackups );
	my( $compat, $relaxed, $strict );
	my( $lock, $keeplock );
	my( $force, $clear, $compress, $small, $split );
	my( $user, $pass, $host, $db );
	my( $pretend, $safetyoff, $debug, $notice, $verbose, $warn );
	my $ok = TRUE;
	my $getoptout = undef;

	my $missingoption = sub {
		my ( $argument ) = @_;

		$getoptout = "value \"$argument\" has been specified with no preceeding option identifier";
		$ok = FALSE;
	}; # missingoption

	Getopt::Long::Configure( 'gnu_getopt' );
	Getopt::Long::Configure( 'no_bundling' );
	eval { GetOptionsFromArray ( \@argv,
	  'b|backup:s'					=> \$action_backup
	,   'lock|lock-database|lock-databases!'	=> \$lock
	,   'keep-lock!'				=> \$keeplock
	,   'small|small-database|small-dataset!'	=> \$small
	,   'compress:s'				=> \$compress
	,   'split|separate-files!'			=> \$split

	, 'r|restore=s'					=> \$action_restore
	, 'i|init:s'					=> \$action_init
	, 'c|check!'					=> \$action_check

	, 'o|mode=s'					=> \$mode
	,   'substitute|versionate|sub!'		=> \$dosub
	,   'marker=s'					=> \$marker

	, 'm|migrate!'					=> \$action_migrate
	, 's|schemata|directory|scripts=s{,}'		=> \@paths
	, 'f|file|filename|schema|script=s'		=> \$file
	,   'description=s'				=> \$desc
	,   'no-backup|no-backups!'			=> \$unsafe
	,   'keep-backup|keep-backups!'			=> \$keepbackups

	,   'clear-metadata!'				=> \$clear
	,   'force!'					=> \$force

	,   'mysql-compat!'				=> \$compat
	,   'mysql-relaxed|relaxed!'			=> \$relaxed

	, 'u|user|username=s'				=> \$user
	, 'p|pass|passwd|password=s'			=> \$pass
	, 'h|host=s'					=> \$host
	, 'd|db|database=s'				=> \$db

	,   'dry-run!'					=> \$pretend
	,   'debug!'					=> \$debug
	, 'n|notice!'					=> \$notice
	, 'w|warn!'					=> \$warn
	, 'v|verbose+'					=> \$verbose
	,   'help|usage!'				=> \$help

	,   '<>'					=>  $missingoption
	#) or die( "$fatal Getopt::Long::GetOptions failed" . ( ( defined $@ and $@ ) ? ": " . $@ : "" ) . "\n" );
	); };
	if( $@ ) {
		$getoptout = $@ if( defined $@ and length( $@ ) );
		$ok = FALSE;
	}

	$ok = FALSE if( ( defined( $file ) and $file ) and ( @paths and scalar( @paths ) ) );
	$ok = FALSE unless( defined( $user ) and $user );
	$ok = FALSE unless( defined( $pass ) and $pass );

	$host = 'localhost' unless( defined( $host ) and $host );

	if( defined( $mode ) and length( $mode ) ) {
		if( $mode =~ m/^\s*schema|schemata\s*$/ ) {
			$mode = 'schema';
		} elsif( $mode =~ m/^\s*(?:stored\s*)?proc(?:edure)?\s*$/ ) {
			$mode = 'procedure';
		} else {
			warn( "Option '--mode' must have value 'schema' or 'procedure'\n" );
			exit( 1 );
		}
	} else {
		$mode = 'schema';
	}

	if( defined( $action_backup ) ) {
		$ok = FALSE if( defined( $db ) and defined( $lock ) );
		# TODO: Support backing-up Stored Procedures separately...
		$ok = FALSE if( 'procedure' eq $mode );
		$ok = FALSE if( defined( $pretend ) );
		$ok = FALSE if( defined( $clear ) );
	} elsif( defined( $action_restore ) ) {
		$ok = FALSE if( defined( $lock ) or defined( $keeplock ) );
		$ok = FALSE if( defined( $compress ) );
		$ok = FALSE if( defined( $small ) );
		$ok = FALSE if( defined( $split ) );
		# TODO: Support restoring Stored Procedures only...
		$ok = FALSE if( 'procedure' eq $mode );
		$ok = FALSE if( defined( $pretend ) );
		$ok = FALSE if( defined( $clear ) );
		$ok = FALSE if( defined( $keepbackups ) );
	} else {
		$ok = FALSE unless( defined( $db ) and $db );
		$ok = FALSE if( defined( $lock ) or defined( $keeplock ) );
		$ok = FALSE if( defined( $compress ) );
		$ok = FALSE if( defined( $small ) );
		$ok = FALSE if( defined( $split ) );
#		$ok = FALSE if( defined( $marker ) and not( defined( $dosub ) ) );
		$ok = FALSE if( defined( $dosub ) and not( 'procedure' eq $mode ) );
		if( not( defined( $action_init ) ) ) {
			$ok = FALSE unless( ( defined( $file ) and $file ) or ( @paths and scalar( @paths ) ) );
		}
	}

	# Set any binary parameters, so there's no further need to check
	# they have been defined() ...
	if( defined( $clear ) and $clear ) {
		$clear = TRUE;
	} else {
		$clear = FALSE;
	}
	if( defined( $compat ) and $compat ) {
		$compat = TRUE;
	} else {
		$compat = FALSE;
	}
	if( defined( $force ) and $force ) {
		$force = TRUE;
	} else {
		$force = FALSE;
	}
	if( defined( $keepbackups ) and $keepbackups ) {
		$keepbackups = TRUE;
	} else {
		$keepbackups = FALSE;
	}
	if( defined( $pretend ) and $pretend ) {
		$pretend = TRUE;
		$safetyoff = FALSE;
	} else {
		$pretend = FALSE;
		$safetyoff = TRUE;
	}
	if( defined( $relaxed ) and $relaxed ) {
		$relaxed = TRUE;
		$strict = FALSE;
	} else {
		$relaxed = FALSE;
		$strict = TRUE;
	}
	if( defined( $small ) and $small ) {
		$small = TRUE;
	} else {
		$small = FALSE;
	}
	if( defined( $split ) and $split ) {
		$split = TRUE;
	} else {
		$split = FALSE;
	}
	if( defined( $unsafe ) and $unsafe ) {
		$unsafe = TRUE;
	} else {
		$unsafe = FALSE;
	}

	if( defined( $lock ) and $lock ) {
		$lock = TRUE;
	} else {
		$lock = FALSE;
	}
	if( defined( $keeplock ) and $keeplock ) {
		$keeplock = TRUE;
		$ok = FALSE unless( $lock );
	} else {
		$keeplock = FALSE;
	}

	if( defined( $dosub ) and $dosub ) {
		$dosub = TRUE;
	} else {
		$dosub = FALSE;
	}

	if( $pretend and $clear ) {
		$ok = FALSE;
	}
	if( $clear and not( $force ) ) {
		$ok = FALSE;
	}

	undef( $user ) unless( defined( $user ) and length( $user ) );
	undef( $pass ) unless( defined( $pass ) and length( $pass ) );
	undef( $host ) unless( defined( $host ) and length( $host ) );
	undef( $db ) unless( defined( $db ) and length( $db ) );
	undef( $mode ) unless( defined( $mode ) and length( $mode ) );
	undef( $marker ) unless( $dosub and defined( $marker ) and length( $marker ) );
	undef( $file ) unless( defined( $file ) and length( $file ) );
	undef( @paths ) unless( @paths and scalar( @paths ) );

	if( ( defined( $help ) and $help ) or ( 0 == scalar( @ARGV ) ) ) {
		my $myway = basename( $0 );
		my $length = length( $myway ) + length( "Usage:  " );
		#                              2         3         4         5         6         7         8
		#                           7890123456789012345678901234567890123456789012345678901234567890
		print(       "Usage: $myway -u <username> -p <password> -h <host> -d <database> ...\n" );
		print( ( " " x $length ) . "<--backup [directory] [:backup options:]|...\n" );
		print( ( " " x $length ) . " --restore <file>|--init [version]>|...\n" );
		print( ( " " x $length ) . "[--migrate|--check] <--scripts <directory>|--file <schema>>...\n" );
		print( ( " " x $length ) . "[[:mode:]] [--mysql-compat] [--no-backup|--keep-backup] ...\n" );
		print( ( " " x $length ) . "[--clear-metadata] [--dry-run] [--force] [--debug] [--verbose]\n" );
		print( "\n" );
		print( ( " " x $length ) . "backup options:   [--compress [:scheme:]] [--small-dataset]\n" );
		print( ( " " x $length ) . "                  [--lock [--keep-lock]] [--separate-files]\n" );
		print( ( " " x $length ) . "scheme:           <gzip|bzip2|xz|lzma>\n" );
		print( "\n" );
		print( ( " " x $length ) . "mode:             --mode <schema|procedure>\n" );
		print( ( " " x $length ) . "                  [--substitute [--marker <marker>]\n" );
		print( "\n" );
		print( ( " " x $length ) . "--mysql-compat   - Required for MySQL prior to v5.6.4\n" );
		print( ( " " x $length ) . "--mysql-relaxed  - Do not operate in STRICT mode\n" );
		print( "\n" );
		print( ( " " x $length ) . "--compress       - Compress backups [using <scheme> compression]\n" );
		print( ( " " x $length ) . "--small-dataset  - Optimise for tables of less than 1GB in size\n" );
		print( ( " " x $length ) . "--lock           - Lock instance for duration of backup\n" );
		print( ( " " x $length ) . "--keep-lock      - Keep lock for up to 24 hours following backup\n" );
		print( "\n" );
		print( ( " " x $length ) . "--substitute     - Replace the string '" . ( ( defined( $marker ) and length( $marker ) ) ? $marker : MARKER ) . "' with version\n" );
		print( ( " " x $length ) . "                   number from stored procedure directory name\n" );
		print( ( " " x $length ) . "--marker         - Use string in place of '" . MARKER . "'\n" );
		print( "\n" );
		print( ( " " x $length ) . "--no-backup      - Do not take backups before making changes\n" );
		print( ( " " x $length ) . "--keep-backup    - Copy backups to a local directory on exit\n" );
		print( ( " " x $length ) . "--clear-metadata - Remove all {my,fly}way metadata tables\n" );
		print( ( " " x $length ) . "--force          - Allow a database to be re-initialised or\n" );
		print( ( " " x $length ) . "                   ignore previous and target versions when\n" );
		print( ( " " x $length ) . "                   applying schema files\n" );
		print( "\n" );
		print( ( " " x $length ) . "--dry-run        - Validate but do not execute schema SQL\n" );
		print( ( " " x $length ) . "--debug          - Output copious debugging statements\n" );
		print( ( " " x $length ) . "--verbose        - Provide more detailed status information\n" );
		exit( 0 );
	} elsif( not( $ok ) ) {
		warn( "Mutually-exclusive arguments '--schema' and '--schemata' cannot both be specified\n" ) if( defined( $file ) and @paths );
		warn( "Mutually-exclusive arguments '--dry-run' and '--clear-metadata' cannot both be specified\n" ) if( $pretend and $clear );
		warn( "Mutually-exclusive arguments '--no-backup' and '--keep-backup' cannot both be specified\n" ) if( $unsafe and $keepbackups );
		warn( "Cannot specify argument '--compress' without option '--backup'\n" ) if( defined( $compress ) and not( defined( $action_backup ) ) );
		warn( "Cannot specify argument '--lock' or '--keep-lock' without option '--backup'\n" ) if( ( $lock or $keeplock ) and not( defined( $action_backup ) ) );
		warn( "Cannot specify argument '--separate-files' without option '--backup'\n" ) if( $split and not( defined( $action_backup ) ) );
		warn( "Cannot specify argument '--keep-lock' without option '--lock'\n" ) if( $keeplock and not( $lock ) );
		warn( "Cannot specify argument '--clear-metadata' without option '--force'\n" ) if( $clear and not( $force ) );
		warn( "Cannot specify argument '--lock' with option '--database' (locks are global)\n" ) if( $lock and defined( $db ) );
#		warn( "Cannot specify argument '--marker' without option '--substitute'\n" ) if( $marker and not( $dosub ) );
		warn( "Cannot specify argument '--substitute' unless option '--mode' is 'procedure'\n" ) if( $dosub and not( 'procedure' eq $mode ) );
		warn( "Required argument '--user' not specified\n" ) unless( defined( $user ) );
		warn( "Required argument '--password' not specified\n" ) unless( defined( $pass ) );
		warn( "Required argument '--host' not specified\n" ) unless( defined( $host ) );
		warn( "Required argument '--database' not specified\n" ) unless( defined( $db ) );
		warn( "Required argument '--schema' or '--schemata' not specified\n" ) unless( defined( $file ) or ( @paths ) or defined( $action_backup ) or defined( $action_restore ) );
		warn( "Command '--restore' takes only a filename as the single argument\n" ) if( defined( $action_restore ) );
		warn( "... additionally, Getopt failed with '$getoptout'\n" ) if( defined( $getoptout ) );
		exit( 1 );
	}

	# -s can be used on a directory in order to determine whether it is
	# empty...
	if( defined( $file ) and ( ( -d $file ) or not ( -s $file ) ) ) {
		warn( "File system object '$file' does not exist, is of zero length, or is not a regular file\n" );
		warn( "(Please use the '--scripts' option to specify multiple input files or directories)\n" );
		exit( 1 );
	}

	if( @paths and scalar( @paths ) ) {
		# TODO: Support multiple descriptions for path invocations?

		warn( "Ignoring --description option '$desc' when invoked with --schemata\n" ) if( defined( $desc ) );
		warn( "Ignoring --description option '$desc' when invoked in Stored Procedure mode\n" ) if( defined( $mode ) and defined( $desc ) );
		$desc = undef;
	}

	$verbose = 1 if( defined( $warn ) and $warn );
	$verbose = 2 if( defined( $notice ) and $notice );
	$verbose = 3 if( defined( $debug ) and $debug );
	$verbosity = $verbose if( defined( $verbose ) );

	# }}}

	#
	# Perform backup, if requested # {{{
	#

	my $auth = {
		  'user'	=> $user
		, 'password'	=> $pass
		, 'host'	=> $host
		, 'port'	=> $port
		, 'database'	=> $db
	};

	if( defined( $action_restore ) and length( $action_restore ) ) {
		dbrestore( $auth, $action_restore );
		die( "Datbase restoration failed for file '$action_restore'\n" );
	}

	if( defined( $action_backup ) ) {
		# --backup may be used alone to trigger a backup, or as
		# --backup=/<dir> or --backup <dir> to specify a destination
		# directory - in which case the assigned value will be the
		# path, rather than '1'...
		#
		my $location;
		if( 1 ne $action_backup ) {
			$location = $action_backup;
			$action_backup = TRUE;
		}

		my $dsn;
		my $dbh;
		my $availabledatabases;
		my $availabletables;

		if( $lock and $keeplock ) {
			# The child must exit before the parent, so
			# we'll fork, lock tables and wait (for a long
			# time) in the parent, and then perform the
			# backup in the child...
			#
			# ... unfortunately, this prevents us from
			# (easily) obtaining an exit status from the
			# child process.
			#
			# ... so what we actually need to do is fork
			# twice, and have the parent call waitpid() on
			# the (more likely to exit) child process
			# running the backup.
			#
			my $firstchildpidorzero = fork;
			die( "fork() failed: $!\n" ) unless( defined( $firstchildpidorzero ) );

			if( 0 == $firstchildpidorzero ) {
				# Child process

				eval {
					setpgrp( 0, 0 );
				};

				# ... this now goes on to perform the
				# backup.
			} else {
				# Parent process

				my $secondchildpidorzero = fork;
				die( "fork() failed: $!\n" ) unless( defined( $secondchildpidorzero ) );

				if( 0 == $secondchildpidorzero ) {
					# Second child process

					eval {
						setpgrp( 0, 0 );
					};

					local $| = 1;

					if( defined( $db ) and length( $db ) ) {
						$dsn = "DBI:mysql:database=$db;host=$host;port=$port";
						print( "\n=> Connecting to database `$db` ...\n" );
					} else {
						$dsn = "DBI:mysql:host=$host;port=$port";
						print( "\n=> Connecting to database instance ...\n" );
					}

					my $error = dbopen( \$dbh, $dsn, $user, $pass, $strict );
					die( $error ."\n" ) if $error;

					if( not ( dosql( $dbh, "FLUSH TABLES WITH READ LOCK" ) ) ) {
						warn( "$warning Failed to globally lock all instance databases' tables\n" );
						$lock = FALSE;
						$keeplock = FALSE;
					} else {
						print( "\n=> All databases on host '$host' are now globally locked for 24 hours, or until" );
						print( "\n=> this process is interupted." );
						print( "\n=> The backup process will continue concurrently.\n" );
					}
					dosql( $dbh, "SELECT(SLEEP(86400))" );

					print( "=> 86400 seconds elapsed, dropping locks and disconnecting.\n" );

					if( $dbh -> ping ) {
						dosql( $dbh, "UNLOCK TABLES" );
						$dbh -> disconnect;
					}

					exit( 0 );

					# End second child process
				} else {
					# Still the (original) parent process

					local $| = 1;

					my $rc;

					if( waitpid( $firstchildpidorzero, 0 ) > 0 ) {
						my( $sig, $core );

						( $rc, $sig, $core ) = ( $? >> 8, $? & 127, $? & 128 );

						if( $core ) {
							warn( "$fatal backup process $firstchildpidorzero core-dumped\n" );
							kill( -15, $secondchildpidorzero ) if( $secondchildpidorzero );
						} elsif( 9 == $sig ) {
							warn( "$warning backup process $firstchildpidorzero was KILLed\n" );
							kill( -15, $secondchildpidorzero ) if( $secondchildpidorzero );
						} else {
							pwarn( "backup process $firstchildpidorzero returned $rc" . ( $sig ? " after signal $sig" : '' ) ) unless( 0 == $rc );

							print( "\n=> All databases on host '$host' remain globally locked for 24 hours, or until" );
							print( "\n=> this process is terminated." );
						}
					} else {
						pwarn( "backup process $firstchildpidorzero disappeared" );
						kill( -15, $secondchildpidorzero ) if( $secondchildpidorzero );
					}

					if( waitpid( $secondchildpidorzero, 0 ) > 0 ) {
						my( $sig, $core );
						( $rc, $sig, $core ) = ( $? >> 8, $? & 127, $? & 128 );
						if( $core ) {
							warn( "$fatal lock process $secondchildpidorzero core-dumped\n" );
						} elsif( 9 == $sig ) {
							warn( "$warning lock process $secondchildpidorzero was KILLed\n" );
						} else {
							pwarn( "lock process $secondchildpidorzero returned $rc" . ( $sig ? " after signal $sig" : '' ) );
						}
					} else {
						pwarn( "lock process $secondchildpidorzero disappeared" );
					}

					exit( $rc );

					# End original parent process
				}
			}
		}

		local $| = 1;

		if( defined( $db ) and length( $db ) ) {
			$dsn = "DBI:mysql:database=$db;host=$host;port=$port";
			print( "\n=> Connecting to database `$db` ...\n" );
		} else {
			$dsn = "DBI:mysql:host=$host;port=$port";
			print( "\n=> Connecting to database instance ...\n" );
		}

		my $error = dbopen( \$dbh, $dsn, $user, $pass, $strict );
		die( $error ."\n" ) if $error;

		if( defined( $db ) and length( $db ) ) {
			$availabletables = getsqlvalues( $dbh, "SHOW TABLES" );
		} else {
			$availabledatabases = getsqlvalues( $dbh, "SHOW DATABASES" );
		}

		if( not( $lock ) ) {
			$dbh -> disconnect;
		} else { # $lock
			if( not( $keeplock ) ) {
				if( not ( dosql( $dbh, "FLUSH TABLES WITH READ LOCK" ) ) ) {
					warn( "$warning Failed to lock tables transaction\n" );
					$lock = FALSE;
					$keeplock = FALSE;
					$dbh -> disconnect;
				}
			}
		}

		# If $auth contains a 'database' entry, then parameter 2 to
		# dbdump(), $objects, specifies the tables to back-up.  If
		# not set, the entire database will be backed-up.  If $auth
		# does not provide a database, then the entire instance will
		# be backed-up.
		# If backing-up an entire instance, the resulting file is
		# written to $location.  If backing-up a single database, then
		# the backup is placed in a directory named $location.  If no
		# $location is specified, then create the backup in the current
		# directory.
		#
		my $success;
		#if( defined( $location ) ) {
			if( defined( $db ) and length( $db ) ) {
				if( not( $split ) or not( $availabletables and scalar( @{ $availabletables } ) ) ) {
					if( not( $availabletables and scalar( @{ $availabletables } ) ) ) {
						print( "!> Unable to retrieve list of tables for database `$db`, backing up all tables to '$location' ...\n" );
					}
					# $location is a file-name ...
					$success = dbdump( $auth, undef, undef, $location, $compress, $small );
				} else {
					# Write per-table files to $location/ ...
					foreach my $table ( @{ $availabletables } ) {
						print( "*> Backing up table `$db`.`$table` to '$location/$db.$table.sql' ...\n" );
						my $tablesuccess = dbdump( $auth, $table, $location, "$db.$table.sql", $compress, $small );
						$success += $tablesuccess;
						print( "!> Table `$table` failed to backup: $tablesuccess\n" ) if( not( $tablesuccess ) );
					}
				}
			} else {
				if( not( $split ) or not( $availabledatabases and scalar( @{ $availabledatabases } ) ) ) {
					if( not( scalar( @{ $availabledatabases } ) ) ) {
						print( "!> Unable to retrieve list of databases for instance, backing up all databases to single file\n" );
					}
					# $location is a directory ...
					$success = dbdump( $auth, undef, $location, undef, $compress, $small );
				} else {
					# Write per-database files to $location/ ...
					foreach my $database ( @{ $availabledatabases } ) {
						next if( qr/^$database$/ |M| [ 'information_schema', 'performance_schema' ] );
						print( "\n*> Backing up database `$database` to '$location/$database.sql' ...\n" );
						my $databasesuccess = dbdump( $auth, $database, $location, "$database.sql", $compress, $small );
						$success += $databasesuccess;
						print( "!> Database `$database` failed to backup: $databasesuccess\n" ) if( not( $databasesuccess ) );
					}
				}
			}
		#} else {
		#	$success = dbdump( $auth, undef, undef, undef, $compress, $small );
		#}

		if( $lock and not( $keeplock ) ) {
			if( $dbh -> ping ) {
				dosql( $dbh, "UNLOCK TABLES" );
				$dbh -> disconnect;
			}
		}

		if( defined( $success) and $success ) {
			print( "Backup process completed successfully\n" );

			exit( 0 );
		} else {
			print( "Backup process failed\n" );

			exit( 1 );
		}

		# Unreachable
		return( undef );
	}

	# }}}

	#
	# Determine file(s) to apply # {{{
	#

	my( @files, $target, $basepath );
	if( @paths and ( 1 == scalar( @paths ) ) ) {
		# Check for /path/*.sql invocations...

		my $path = $paths[ 0 ];
		my $pattern;

		if( -d $path ) {
			my $actualpath = realpath( $path );
			if( not( -d $actualpath ) ) {
				die( "$fatal Specified path '$path' does not appear to resolve to a directory\n" );
			}
			$path = $actualpath;
			$pattern = "*";

		} else {
			if( not( -s $path ) ) {
				die( "$fatal Object '$path' does not exist or cannot be read\n" );
			}
			my $pathprefix = dirname( realpath( $path ) );
			if( not( -d $pathprefix ) ) {
				die( "$fatal Apparent parent directory '$pathprefix' of file '$path' does not appear to resolve to a directory\n" );
			}
			#( $pattern = $path ) =~ s|^.*/([^/]+)$|$1|;
			$pattern = basename( $path );
			$path = $pathprefix;
		}

		$path = '.' unless( defined( $path ) and length( $path ) );
		$basepath = $path;
		@files = bsd_glob( $basepath . "/" . $pattern );
		if( scalar( @files ) ) {
			#$target = \@files;
			my @targetfiles;
			foreach my $file ( @files ) {
				push( @targetfiles, $file ) if( not( -d $file ) and -s $file );
			}
			$target = \@targetfiles;
		} else {
			die( "$fatal No files match pattern '$pattern' in directory '$basepath'\n" );
		}

	} elsif( @paths and scalar( @paths ) ) {
		$target = \@paths;

	} else {
		if( not( defined( $file ) and length( $file ) ) ) {
			die( "File name required\n" ) unless( defined( $action_init ) );
		} else {
			die( "$fatal Cannot read from file '$file'\n" ) unless( defined( $file ) and -r $file );
		}
	}

	if( defined( $target ) ) {
		# If we're applying Stored Procedures, we assume that
		# they are versioned by directory, and so we don't care
		# what they are called or what order they are applied
		# in, but they have to all be in the same place!
		# Note, however, that the adoption of symlinks causes problems
		# if we use 'realpath' indiscriminately...
		if( 'procedure' eq $mode ) {
			#my $path = realpath( @{ $target }[ 0 ] );
			#if( not( -d $path ) ) {
				#$path = dirname( $path );
				my $path = dirname( @{ $target }[ 0 ] );
				if( not( -d $path ) ) {
					die( "$fatal Cannot resolve directory name for path '" . @{ $target }[ 0 ] . "'\n" );
				}
			#}
			my $okay = TRUE;
			my $index = -1; # Will be incremented before use...
			PROCFILE: foreach my $singlefile ( @{ $target } ) {
				#my $singlepath = realpath( $singlefile );
				#if( not( -d $singlepath ) ) {
					#$singlepath = dirname( $singlepath );
					my $singlepath = dirname( $singlefile );
					if( not( -d $singlepath ) ) {
						$singlepath = undef;
						$okay = FALSE;
						warn( "$fatal Cannot resolve directory name for path '$singlefile'\n" );
					}
				#}
				if( defined( $singlepath ) and not( $singlepath eq $path ) ) {
					$okay = FALSE;
					warn( "$fatal Directory path for file '$singlefile' does not fall within detected common directory '$path'\n" );
				}
				$index ++;
				if( basename( $singlefile ) =~ m/\.metadata$/ ) {
					pdebug( "Excluding metadata file '$singlefile' ..." );
					splice( $target, $index, 1 );
					next PROCFILE;
				}
			}
			exit( 1 ) unless( $okay );
			$path = '.' unless( defined( $path ) and length( $path ) );
			$basepath = $path;
			@files = @{ $target };
		} else {
			#@files = i3_keysort { ( my $version = $_ ) =~ s/^V([\d.])+__.*$/$1/; return( split( /\./, $version ) ); } @{ $target };
			#my @sortedfiles = sort { ( $a =~ /^V([\d.]+)__/ )[ 0 ] <=> ( $b =~ /^V([\d.]+)__/ )[ 0 ] } @{ $target };
                        foreach my $index ( 0 .. scalar( @{ $target } ) ) {
                                my $file = @{ $target }[ $index ];
                                if( not( length( $file ) ) or ( $file =~ m/^\s*$/ ) ) {
                                        delete @{ $target }[ $index ];
                                } else {
                                        my $version = ( $file  =~ /V([\d.]+)__/ )[ 0 ];
                                        warn( "$warning Target '$file' has invalid name without an identifiable version" ) unless ( defined( $version ) and length( $version ) );
                                }
                        }
                        @files = sort { versioncmp( ( $a =~ /V([\d.]+)__/ )[ 0 ], ( $b =~ /V([\d.]+)__/ )[ 0 ] ) } @{ $target };
		}
	}

	if( 'procedure' eq $mode ) {
		if( not( defined( $basepath ) ) ) {
			die( "$fatal Base directory for Stored Procedures not defined\n" );
		} elsif( not -d $basepath ) {
			die( "$fatal Directory '$basepath' does not exist\n" );
		} elsif( not( -s $basepath . '/' . $db . '.metadata' ) ) {
			die( "$fatal Metadata file '" . $db . '.metadata' . "' for database `$db` is not present in directory '$basepath' or cannot be read\n" );
		}
	}

	print( "=> Processing " . ( 'procedure' eq $mode ? 'Stored Procedures' : 'files' ) . ":\n" );
	foreach my $item ( @files ) {
		print( "=>  $item\n" );
	}
	print( "\n" );

	my $tmpdir;
	if( $safetyoff and not( $unsafe ) ) {
		$tmpdir = File::Temp -> newdir() or die( "Temporary directory creation failed: $!, $@\n" );
		pdebug( "Using temporary directory '$tmpdir' ..." );
	}

	my $backupdir;
	{
		my ( $sec, $min, $hour, $mday, $mon, $year, $wday, $yday, $isdst ) = localtime( time );
		$year += 1900;
		printf( "=> %s starting at %04d/%02d/%02d %02d:%02d.%02d\n\n", $0, $year, $mon, $mday, $hour, $min, $sec );

		my( $file, $path, $ext ) = fileparse( realpath( $0 ), qr/\.[^.]+/ );
		$backupdir = sprintf( "%s-backup.%04d%02d%02d.%02d%02d%02d", $file, $year, $mon, $mday, $hour, $min, $sec );
	}

	# }}}

	#
	# Create database, but only if --init is used # {{{
	#

	if( defined( $action_init ) and $safetyoff ) {
		print( "\n=> '--init' specified, ensuring that database `$db` exists ...\n" );
		my $dsn = "DBI:mysql:host=$host;port=$port";
		my $dbh;
		my $error = dbopen( \$dbh, $dsn, $user, $pass, $strict, { RaiseError => 0, PrintError => 0 } );
		die( $fatal . ' ' . $error . "\n" . ' ' x length( $fatal ) . " Is the database instance running?\n" ) if $error;

		dosql( $dbh, "CREATE DATABASE IF NOT EXISTS `$db`" ) or die( "Failed to create database: " . $dbh -> errstr() . "\n" );

		print( "\n=> Disconnecting from database.\n" );
		$dbh -> disconnect;
	}

	# }}}

	#
	# Open mysql database connection to ensure metadata tables exist # {{{
	#

	print( "\n=> Connecting to database `$db` ...\n" );
	my $dsn = "DBI:mysql:database=$db;host=$host;port=$port";
	my $dbh;
	my $error = dbopen( \$dbh, $dsn, $user, $pass, $strict, { RaiseError => 0, PrintError => 0 } );
	die( $fatal . ' ' . $error . "\n" . ' ' x length( $fatal ) . "(Databases will be auto-created on --init when not in dry-run mode)\n" ) if $error;

	#
	# Create {fl,m}yway metadata tables
	#

	if( $clear ) { # and $safetyoff
		if( 'procedure' eq $mode ) {
			dosql( $dbh, "DROP TABLE `$mywayprocsname`" );
		} else {
			dosql( $dbh, "DROP TABLE `$flywaytablename`" );
			dosql( $dbh, "DROP TABLE `$mywayactionsname`" );
			dosql( $dbh, "DROP TABLE `$mywaytablename`" );
		}
	}

	my @tables;
	#if( 'procedure' eq $mode ) {
	#	@tables = (
	#		  { 'name' => 'myway',  'table' => $mywayprocsname,   'ddl' => $mywayprocsddl,   'action' => "SELECT * FROM $mywayprocsname ORDER BY `started`" }
	#	);
	#} else {
	#	@tables = (
	#		  { 'name' => 'Flyway', 'table' => $flywaytablename,  'ddl' => $flywayddl,       'action' => "SELECT * FROM $flywaytablename ORDER BY `version`" }
	#		, { 'name' => 'myway',  'table' => $mywaytablename,   'ddl' => $mywayddl,        'action' => "SELECT * FROM $mywaytablename ORDER BY `started`" }
	#		, { 'name' => 'myway',  'table' => $mywayactionsname, 'ddl' => $mywayactionsddl, 'action' => "SELECT COUNT(*) FROM $mywayactionsname" }
	#	);
	#}
	@tables = (
		  { 'name' => 'Flyway', 'table' => $flywaytablename,  'ddl' => $flywayddl,       'action' => "SELECT * FROM $flywaytablename ORDER BY `version` DESC LIMIT 5" }
		, { 'name' => 'myway',  'table' => $mywaytablename,   'ddl' => $mywayddl,        'action' => "SELECT * FROM $mywaytablename ORDER BY `started` DESC LIMIT 5" }
		, { 'name' => 'myway',  'table' => $mywayprocsname,   'ddl' => $mywayprocsddl,   'action' => "SELECT * FROM $mywayprocsname ORDER BY `started` DESC LIMIT 5" }
		, { 'name' => 'myway',  'table' => $mywayactionsname, 'ddl' => $mywayactionsddl, 'action' => "SELECT COUNT(*) FROM $mywayactionsname" }
	);
	foreach my $table ( @tables ) {
		my $name   = $table -> { 'name'   };
		my $tname  = $table -> { 'table'  };
		my $ddl    = $table -> { 'ddl'    };
		my $action = $table -> { 'action' };

		if( $compat and $ddl =~ m/\stimestamp\([0-6]\)\s/i ) {
			print( "\n*> Removing micro-second precision from definition for <mysql-5.6.4 compatibility ...\n" );
			$ddl =~ s/(\stimestamp)\([0-6]\)(\s)/$1$2/gi;
		}

		if( $pretend ) {
			print( "\nS> Would ensure that $name `$tname` table exists.\n" );
		} else {
			print( "\n=> Ensuring that $name `$tname` table exists ...\n" );
			dosql( $dbh, $ddl ) or die( "Table creation failed\n" );

			eval {
				if( defined( $action ) and length( $action ) ) {
					formatastable( $dbh, $action, '   ' );
				} else {
					formatastable( $dbh, "DESCRIBE `$tname`", '   ' );
					#formatastable( $dbh, "SELECT * FROM `$tname`", '   ' );
				}
				print( "\n" );
			};
			if( $@ ) {
				if( $pretend ) {
					pwarn( "Table `$table` does not exist, but will be created on a full run" );
				} else {
					die( "Essential meta-data table `$table` is missing - cannot continue\n" );
				}
			}

			# Older myway.pl releases lacked a `sqlstarted`
			# attribute on metadata tables, and so could not
			# differentiate between when backups commenced and when
			# we actually started executing a SQL statement - let's fix this ;)
			#
			if( $tname eq $mywaytablename ) {
				my $st = "DESCRIBE `$tname`";
				my $sth = executesql( $dbh, undef, $st );
				if( not( defined( $sth ) and $sth ) ) {
					warn( "Unable to create statement handle to execute '$st': " . $dbh -> errstr() . "\n" );
				} else {
					my $foundexecutionstarted = FALSE;

					while( my $ref = $sth -> fetchrow_arrayref() ) {
						my $field = @{ $ref }[ 0 ];
						my $type = @{ $ref }[ 1 ];

						# XXX: Hard-coded table structure :(
						if( $field eq 'sqlstarted' ) {
							$foundexecutionstarted = TRUE;
						}
					}

					if( not( $foundexecutionstarted ) ) {
						# XXX: Hard-coded SQL
						#
						eval {
							if ( dosql( $dbh, "ALTER TABLE `$tname` ADD COLUMN `sqlstarted` TIMESTAMP NULL DEFAULT NULL AFTER `started`" ) ) {
								print( "=> Additional timing column for table `$tname` added\n" );
							} else {
								print( "*> Additional timing column for table `$tname` could not be added\n" );
							}
						};
					}

					## XXX: Try to fix-up strict-mode's NO_ZERO_DATE requirement...
					#eval {
					#	#if ( dosql( $dbh, "UPDATE IGNORE `$tname` SET `sqlstarted` = NULL WHERE DATE(`sqlstarted`) = DATE('0000-00-00 00:00:00')" ) ) {
					#	if ( dosql( $dbh, "UPDATE `$tname` SET `sqlstarted` = DATE('1970-01-01 00:00:01') WHERE DATE(`sqlstarted`) = DATE('0000-00-00 00:00:00') OR `sqlstarted` = NULL" ) ) {
					#		print( "=> Invalid timing values in table `$tname` removed\n" );
					#	} else {
					#		print( "*> Invalid timing values in table `$tname` could not be removed\n" );
					#	}
					#};

					$sth -> finish();
				}
			}

			# If we've dropped into MySQL compatibility mode
			# previously (as above) then revert the change now...
			#
			if( ( $tname eq $mywayactionsname ) and not( $compat ) ) {
				my $st = "DESCRIBE `$tname`";
				my $sth = executesql( $dbh, undef, $st );
				if( not( defined( $sth ) and $sth ) ) {
					warn( "Unable to create statement handle to execute '$st': " . $dbh -> errstr() . "\n" );
				} else {
					my $foundoldstatementtype = FALSE;

					while( my $ref = $sth -> fetchrow_arrayref() ) {
						my $field = @{ $ref }[ 0 ];
						my $type = @{ $ref }[ 1 ];

						# XXX: Hard-coded table structure :(
						if( ( $field eq 'started' ) and ( $type =~ m/timestamp/i ) ) {
							if( lc( $type ) eq 'timestamp' ) {
								# XXX: Hard-coded SQL
								#
								if ( dosql( $dbh, "ALTER TABLE `$tname` MODIFY `started` TIMESTAMP(6) NOT NULL DEFAULT CURRENT_TIMESTAMP" ) ) {
									print( "=> MySQL compatibility option on table `$tname` removed\n" );
								} else {
									print( "*> MySQL compatibility option on table `$tname` could not be removed\n" );
								}
							}
						} elsif( ( $field eq 'statement' ) and ( $type =~ m/varchar/i ) ) {
							# XXX: Hard-coded SQL
							#
							if ( dosql( $dbh, "ALTER TABLE `$tname` MODIFY `statement` LONGTEXT CHARACTER SET 'UTF8' NOT NULL" ) ) {
								print( "=> Statement length limitations on table `$tname` removed\n" );
							} else {
								print( "*> Statement length limitations on table `$tname` could not be removed\n" );
							}
						}
					}

					$sth -> finish();
				}
			}
		}
	}

	print( "\n=> Disconnecting from database.\n" );
	$dbh -> disconnect;

	# }}}

	#
	# Apply schema file to database # {{{
	#

	my $actions;
	$actions -> { 'check' }       = $action_check;
	$actions -> { 'init' }        = $action_init;
	$actions -> { 'migrate' }     = $action_migrate;

	my $variables;
	$variables -> { 'mode' }      = $mode;
	$variables -> { 'marker' }    = $marker if( $dosub );
	$variables -> { 'first' }     =  not( 'procedure' eq $mode );
	$variables -> { 'backupdir' } = $backupdir;
	$variables -> { 'clear' }     = $clear;
	$variables -> { 'compat' }    = $compat;
	$variables -> { 'desc' }      = $desc;
	$variables -> { 'force' }     = $force;
	$variables -> { 'pretend' }   = $pretend;
	$variables -> { 'safetyoff' } = $safetyoff;
	$variables -> { 'strict' }    = $strict;
	$variables -> { 'tmpdir' }    = $tmpdir;
	$variables -> { 'unsafe' }    = $unsafe;

	my $version = undef;

	if( scalar( @files ) ) {
		@files = ( shift( @files ) ) if( defined( $action_init ) );

		foreach my $item ( @files ) {
			if( -r $item ) {
				print "*> Processing file '$item' ...\n";
				eval {
					if( defined( $version ) ) {
						$version = applyschema( $item, $actions, $variables, $auth, $version );
					} else {
						$version = applyschema( $item, $actions, $variables, $auth );
					}
					if( not( defined( $version ) ) ) {
						if( $pretend ) {
							die( "applyversion() returned undef\n" );
						}
					} elsif( ref( $version ) eq 'SCALAR' ) {
						print( "*> This session now has base version '${ $version }'\n" );
					} elsif( ref( $version ) eq '' ) {
						if( not( $version ) ) {
							die( "applyschema() failed\n" );
						}
					} else {
						warn( "applyschema() returned invalid data '$version':\n" );
						print Data::Dumper -> Dump( [ $version ], [ qw( *version ) ] );
						die( "applyschema() returned invalid response\n" );
					}
				};
				if( $@ ) {
					#warn( "Failed with error: " . $@ . "\n" );
					#warn( "$fatal " . $@ . "\n" );
					#die( "Aborted\n" );
					#disable diagnostics;
					die( "$fatal " . $@ . "\n" );
					# Unreachable
					#enable diagnostics;
				}
				$variables -> { 'first' } = FALSE if( $variables -> { 'first' } );
			} else {
				warn( "$warning Cannot read from file '$item' - skipping\n" );
			}
		}
	} else {
		eval {
			die( "applyschema() failed\n" ) unless( applyschema( $file, $actions, $variables, $auth ) );
		};
		if( $@ ) {
			#warn( "Failed with error: " . $@ . "\n" );
			#warn( "$fatal " . $@ . "\n" );
			#die( "Aborted\n" );
			#disable diagnostics;
			die( "$fatal " . $@ . "\n" );
			# Unreachable
			#enable diagnostics;
		}
	}

	if( not( 'procedure' eq $mode ) and defined( $tmpdir ) ) {
		if( $keepbackups ) {
			make_path( $backupdir, {
				  mode		=> 0775
				, verbose	=> FALSE
				, error		=> \my $errors
			} );
			if( @{ $errors } ) {
				foreach my $entry ( @{ $errors } ) {
					my( $dir, $message ) = %{ $entry };
					if( length( $message ) ) {
						print STDERR "Error creating directory '$dir': $message";
					} else {
						print STDERR "make_path general error: $message";
					}
				}
				return( undef );
			}

			print( "\n=> Moving temporary backups to '$backupdir' ...\n" );
			foreach my $file ( <$tmpdir/*> ) {
				move( $file, $backupdir . '/' ) or warn( "Failed to move file '$file' to destination '$backupdir/': $@\n" );
			}
			print( "=> Backups relocated\n" );
		}
	}

	# }}}

	exit( 0 );
} # main # }}}

main( @ARGV );

1;

}

# vi: set filetype=perl syntax=perl commentstring=#%s foldmarker=\ {{{,\ }}} foldmethod=marker colorcolumn=80:
