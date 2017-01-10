/* -----------------------------------------------------------------------------
 *
 * (c) The GHC Team, 2008-2017
 *
 * Support for fast binary event logging.
 *
 * ---------------------------------------------------------------------------*/

#ifndef EVENTLOG_WRITER_H
#define EVENTLOG_WRITER_H

#ifdef HAVE_UNISTD_H
#include <unistd.h>
#endif

#include "PosixSource.h"
#include "Rts.h"

/*
 *  Abstraction for writing eventlog data.
 */
typedef struct {
    // Initialize an EventLogOutput for writing eventlogs.
    void (* initEventLogWriter) (void);

    // Write a series of events.
    int (* writeEventLog) (unsigned char *eventlog, size_t eventlog_size);

    // Flush possibly existing buffers
    void (* flushEventLog) (void);

    // Close an initialized EventLogOutput.
    void (* stopEventLogWriter) (void);
} EventLogWriter;

/*
 * An EventLogWriter which writes eventlogs to
 * a file `program.eventlog`.
 */
void initEventLogFileWriter(void);

int writeEventLogFile(unsigned char *eventlog, size_t eventlog_size);

void flushEventLogFile(void);

void stopEventLogFileWriter(void);

#endif /* EVENTLOG_WRITER_H */
