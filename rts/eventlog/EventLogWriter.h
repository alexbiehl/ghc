/* -----------------------------------------------------------------------------
 *
 * (c) The GHC Team, 2008-2017
 *
 * Support for fast binary event logging.
 *
 * ---------------------------------------------------------------------------*/

#ifndef EVENTLOG_WRITER_H
#define EVENTLOG_WRITER_H

#include "PosixSource.h"
#include "Rts.h"

#include "BeginPrivate.h"

/*
 *  Abstraction for writing eventlog data.
 */
typedef struct {
    // Initialize an EventLogOutput for writing eventlogs.
    void (* initEventLogWriter) (void);

    // Write a series of events.
    StgInt (* writeEventLog) (StgInt8 *, StgWord64);

    // Flush possibly existing buffers
    void (* flushEventLog) (void);

    // Close an initialized EventLogOutput.
    void (* stopEventLogWriter) (void);
} EventLogWriter;

/*
 * An EventLogWriter which writes eventlogs to
 * a file `program.eventlog`.
 */
extern EventLogWriter fileEventLogWriter;

#include "EndPrivate.h"

#endif /* EVENTLOG_WRITER_H */
