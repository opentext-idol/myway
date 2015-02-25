myway
=====

# A MySQL-targeted, enhanced Flyway alternative written in perl

We love the [Flyway](http://flywaydb.org/getstarted/) concept of simply
managing database schema files and migrations, and storing this version data
within the database to allow for updates to be unambiguously tracked.

However, we also found several issues with the implementation, certainly when
running against [MySQL](https://mariadb.org/):

* Flyway opens two database connections simultaneously, and then proceeds to
  use one to perform the specified schema changes.  If these changes take too
  long then the second, otherwise unused, connection will time-out.  Once the
  changes are complete, Flyway tries to use the second connection to update
  its schema table with the confirmation of the update.  If this connection
  is no longer valid, then Flyway will hang without having committed its data;

* In this case, the database will require manual recovery before Flyway can
  proceed - either to manually write the metadata entry, or to revert the
  database state change;

* Flyway makes no effort to take any backups before making database alterations
  or to rollback on failure;

* Flyway produces no feedback whilst in operation to allow a DBA to track the
  progress of a given change.

As we repeatedly ran into these issues, we deicded that it was justified to
spend development time producing a compatible alternative that allows for
interoperability with Flyway whlist addressing the above issues.  myway also
supports the loading of versioned Stored Procedures with logic to allow for
easy version migration with version '(n-1)' maintained with version 'n'.

As use of myway increased, it has gathered new features and can be used to
take and restore full-instance, per-database, or per-table backups and supports
a rich versioning scheme whereby the order in which to apply schema updates are
encoded within the metadata of the schema file.

In addition, further metadata is written specifying exactly what commands are
executed against the database, the user running these changes and the source
host and file, as well as full timing data.

The most significant diversion from Flyway is that the Flyway 'schema_version'
metadata table contains a 'checksum' field which is never populated in myway,
as we instead store an sha1sum of the source file in the 'myway_schema_version'
myway metadata table.
